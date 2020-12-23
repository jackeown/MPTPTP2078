%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:48 EST 2020

% Result     : Theorem 2.92s
% Output     : CNFRefutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 232 expanded)
%              Number of leaves         :   33 ( 113 expanded)
%              Depth                    :   11
%              Number of atoms          :  233 (1896 expanded)
%              Number of equality atoms :    1 (   3 expanded)
%              Maximal formula depth    :   27 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v5_pre_topc > v1_funct_2 > v4_pre_topc > v3_pre_topc > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k1_partfun1 > k3_funct_2 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

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

tff(f_189,negated_conjecture,(
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

tff(f_45,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => m1_subset_1(k3_funct_2(A,B,C,D),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_funct_2)).

tff(f_62,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v3_pre_topc(B,A)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_tops_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_142,axiom,(
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

tff(f_91,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_28,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_44,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_42,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_40,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_38,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_36,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_79,plain,(
    ! [A_223,B_224,C_225,D_226] :
      ( m1_subset_1(k3_funct_2(A_223,B_224,C_225,D_226),B_224)
      | ~ m1_subset_1(D_226,A_223)
      | ~ m1_subset_1(C_225,k1_zfmisc_1(k2_zfmisc_1(A_223,B_224)))
      | ~ v1_funct_2(C_225,A_223,B_224)
      | ~ v1_funct_1(C_225)
      | v1_xboole_0(A_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_81,plain,(
    ! [D_226] :
      ( m1_subset_1(k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',D_226),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(D_226,u1_struct_0('#skF_5'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0(u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_36,c_79])).

tff(c_86,plain,(
    ! [D_226] :
      ( m1_subset_1(k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',D_226),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(D_226,u1_struct_0('#skF_5'))
      | v1_xboole_0(u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_81])).

tff(c_90,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_73,plain,(
    ! [A_221] :
      ( m1_subset_1('#skF_1'(A_221),k1_zfmisc_1(u1_struct_0(A_221)))
      | ~ l1_pre_topc(A_221)
      | ~ v2_pre_topc(A_221)
      | v2_struct_0(A_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_xboole_0(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_77,plain,(
    ! [A_221] :
      ( v1_xboole_0('#skF_1'(A_221))
      | ~ v1_xboole_0(u1_struct_0(A_221))
      | ~ l1_pre_topc(A_221)
      | ~ v2_pre_topc(A_221)
      | v2_struct_0(A_221) ) ),
    inference(resolution,[status(thm)],[c_73,c_2])).

tff(c_93,plain,
    ( v1_xboole_0('#skF_1'('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_90,c_77])).

tff(c_96,plain,
    ( v1_xboole_0('#skF_1'('#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_93])).

tff(c_97,plain,(
    v1_xboole_0('#skF_1'('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_96])).

tff(c_10,plain,(
    ! [A_8] :
      ( ~ v1_xboole_0('#skF_1'(A_8))
      | ~ l1_pre_topc(A_8)
      | ~ v2_pre_topc(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_100,plain,
    ( ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_97,c_10])).

tff(c_103,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_100])).

tff(c_105,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_103])).

tff(c_106,plain,(
    ! [D_226] :
      ( m1_subset_1(k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',D_226),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(D_226,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_50,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_48,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_56,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_54,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_34,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_32,plain,(
    v1_funct_2('#skF_7',u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_30,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_26,plain,(
    r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_162,plain,(
    ! [C_244,E_239,B_243,F_240,A_242,D_241] :
      ( r1_tmap_1(B_243,A_242,k1_partfun1(u1_struct_0(B_243),u1_struct_0(C_244),u1_struct_0(C_244),u1_struct_0(A_242),D_241,E_239),F_240)
      | ~ r1_tmap_1(C_244,A_242,E_239,k3_funct_2(u1_struct_0(B_243),u1_struct_0(C_244),D_241,F_240))
      | ~ r1_tmap_1(B_243,C_244,D_241,F_240)
      | ~ m1_subset_1(k3_funct_2(u1_struct_0(B_243),u1_struct_0(C_244),D_241,F_240),u1_struct_0(C_244))
      | ~ m1_subset_1(F_240,u1_struct_0(B_243))
      | ~ m1_subset_1(E_239,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_244),u1_struct_0(A_242))))
      | ~ v1_funct_2(E_239,u1_struct_0(C_244),u1_struct_0(A_242))
      | ~ v1_funct_1(E_239)
      | ~ m1_subset_1(D_241,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_243),u1_struct_0(C_244))))
      | ~ v1_funct_2(D_241,u1_struct_0(B_243),u1_struct_0(C_244))
      | ~ v1_funct_1(D_241)
      | ~ l1_pre_topc(C_244)
      | ~ v2_pre_topc(C_244)
      | v2_struct_0(C_244)
      | ~ l1_pre_topc(B_243)
      | ~ v2_pre_topc(B_243)
      | v2_struct_0(B_243)
      | ~ l1_pre_topc(A_242)
      | ~ v2_pre_topc(A_242)
      | v2_struct_0(A_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_22,plain,(
    ~ r1_tmap_1('#skF_5','#skF_4',k1_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_6','#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_168,plain,
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
    inference(resolution,[status(thm)],[c_162,c_22])).

tff(c_172,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_4','#skF_7',k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_8'))
    | ~ m1_subset_1(k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_8'),u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_44,c_42,c_56,c_54,c_40,c_38,c_36,c_34,c_32,c_30,c_28,c_26,c_168])).

tff(c_173,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_4','#skF_7',k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_8'))
    | ~ m1_subset_1(k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_8'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_46,c_58,c_172])).

tff(c_174,plain,(
    ~ m1_subset_1(k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_8'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_173])).

tff(c_177,plain,(
    ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_106,c_174])).

tff(c_181,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_177])).

tff(c_182,plain,(
    ~ r1_tmap_1('#skF_3','#skF_4','#skF_7',k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_173])).

tff(c_24,plain,(
    v5_pre_topc('#skF_7','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_183,plain,(
    m1_subset_1(k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_8'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_173])).

tff(c_14,plain,(
    ! [B_22,A_10,C_28,D_31] :
      ( r1_tmap_1(B_22,A_10,C_28,D_31)
      | ~ m1_subset_1(D_31,u1_struct_0(B_22))
      | ~ v5_pre_topc(C_28,B_22,A_10)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_22),u1_struct_0(A_10))))
      | ~ v1_funct_2(C_28,u1_struct_0(B_22),u1_struct_0(A_10))
      | ~ v1_funct_1(C_28)
      | ~ l1_pre_topc(B_22)
      | ~ v2_pre_topc(B_22)
      | v2_struct_0(B_22)
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_185,plain,(
    ! [A_10,C_28] :
      ( r1_tmap_1('#skF_3',A_10,C_28,k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_8'))
      | ~ v5_pre_topc(C_28,'#skF_3',A_10)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(A_10))))
      | ~ v1_funct_2(C_28,u1_struct_0('#skF_3'),u1_struct_0(A_10))
      | ~ v1_funct_1(C_28)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(resolution,[status(thm)],[c_183,c_14])).

tff(c_188,plain,(
    ! [A_10,C_28] :
      ( r1_tmap_1('#skF_3',A_10,C_28,k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_8'))
      | ~ v5_pre_topc(C_28,'#skF_3',A_10)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(A_10))))
      | ~ v1_funct_2(C_28,u1_struct_0('#skF_3'),u1_struct_0(A_10))
      | ~ v1_funct_1(C_28)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_185])).

tff(c_198,plain,(
    ! [A_247,C_248] :
      ( r1_tmap_1('#skF_3',A_247,C_248,k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_8'))
      | ~ v5_pre_topc(C_248,'#skF_3',A_247)
      | ~ m1_subset_1(C_248,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(A_247))))
      | ~ v1_funct_2(C_248,u1_struct_0('#skF_3'),u1_struct_0(A_247))
      | ~ v1_funct_1(C_248)
      | ~ l1_pre_topc(A_247)
      | ~ v2_pre_topc(A_247)
      | v2_struct_0(A_247) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_188])).

tff(c_201,plain,
    ( r1_tmap_1('#skF_3','#skF_4','#skF_7',k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_8'))
    | ~ v5_pre_topc('#skF_7','#skF_3','#skF_4')
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_7')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_198])).

tff(c_204,plain,
    ( r1_tmap_1('#skF_3','#skF_4','#skF_7',k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_8'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_34,c_32,c_24,c_201])).

tff(c_206,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_182,c_204])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:01:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.92/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.53  
% 3.02/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.53  %$ r1_tmap_1 > v5_pre_topc > v1_funct_2 > v4_pre_topc > v3_pre_topc > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k1_partfun1 > k3_funct_2 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_8 > #skF_4
% 3.02/1.53  
% 3.02/1.53  %Foreground sorts:
% 3.02/1.53  
% 3.02/1.53  
% 3.02/1.53  %Background operators:
% 3.02/1.53  
% 3.02/1.53  
% 3.02/1.53  %Foreground operators:
% 3.02/1.53  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.02/1.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.02/1.53  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.02/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.02/1.53  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.02/1.53  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.02/1.53  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.02/1.53  tff('#skF_7', type, '#skF_7': $i).
% 3.02/1.53  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.02/1.53  tff('#skF_5', type, '#skF_5': $i).
% 3.02/1.53  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.02/1.53  tff('#skF_6', type, '#skF_6': $i).
% 3.02/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.02/1.53  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.02/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.02/1.53  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.02/1.53  tff('#skF_8', type, '#skF_8': $i).
% 3.02/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.02/1.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.02/1.53  tff('#skF_4', type, '#skF_4': $i).
% 3.02/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.02/1.53  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 3.02/1.53  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.02/1.53  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.02/1.53  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.02/1.53  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 3.02/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.02/1.53  
% 3.02/1.56  tff(f_189, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((~v2_struct_0(C) & v2_pre_topc(C)) & l1_pre_topc(C)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(C), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(A))))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => ((r1_tmap_1(C, A, D, F) & v5_pre_topc(E, A, B)) => r1_tmap_1(C, B, k1_partfun1(u1_struct_0(C), u1_struct_0(A), u1_struct_0(A), u1_struct_0(B), D, E), F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_tmap_1)).
% 3.02/1.56  tff(f_45, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => m1_subset_1(k3_funct_2(A, B, C, D), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_funct_2)).
% 3.02/1.56  tff(f_62, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: (((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v3_pre_topc(B, A)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_tops_1)).
% 3.02/1.56  tff(f_32, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 3.02/1.56  tff(f_142, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((~v2_struct_0(C) & v2_pre_topc(C)) & l1_pre_topc(C)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(C))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(C))))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(A))))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((((G = k3_funct_2(u1_struct_0(B), u1_struct_0(C), D, F)) & r1_tmap_1(B, C, D, F)) & r1_tmap_1(C, A, E, G)) => r1_tmap_1(B, A, k1_partfun1(u1_struct_0(B), u1_struct_0(C), u1_struct_0(C), u1_struct_0(A), D, E), F)))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_tmap_1)).
% 3.02/1.56  tff(f_91, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (v5_pre_topc(C, B, A) <=> (![D]: (m1_subset_1(D, u1_struct_0(B)) => r1_tmap_1(B, A, C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_tmap_1)).
% 3.02/1.56  tff(c_52, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_189])).
% 3.02/1.56  tff(c_28, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_189])).
% 3.02/1.56  tff(c_46, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_189])).
% 3.02/1.56  tff(c_44, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_189])).
% 3.02/1.56  tff(c_42, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_189])).
% 3.02/1.56  tff(c_40, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_189])).
% 3.02/1.56  tff(c_38, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_189])).
% 3.02/1.56  tff(c_36, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_189])).
% 3.02/1.56  tff(c_79, plain, (![A_223, B_224, C_225, D_226]: (m1_subset_1(k3_funct_2(A_223, B_224, C_225, D_226), B_224) | ~m1_subset_1(D_226, A_223) | ~m1_subset_1(C_225, k1_zfmisc_1(k2_zfmisc_1(A_223, B_224))) | ~v1_funct_2(C_225, A_223, B_224) | ~v1_funct_1(C_225) | v1_xboole_0(A_223))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.02/1.56  tff(c_81, plain, (![D_226]: (m1_subset_1(k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', D_226), u1_struct_0('#skF_3')) | ~m1_subset_1(D_226, u1_struct_0('#skF_5')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | v1_xboole_0(u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_36, c_79])).
% 3.02/1.56  tff(c_86, plain, (![D_226]: (m1_subset_1(k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', D_226), u1_struct_0('#skF_3')) | ~m1_subset_1(D_226, u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_81])).
% 3.02/1.56  tff(c_90, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_86])).
% 3.02/1.56  tff(c_73, plain, (![A_221]: (m1_subset_1('#skF_1'(A_221), k1_zfmisc_1(u1_struct_0(A_221))) | ~l1_pre_topc(A_221) | ~v2_pre_topc(A_221) | v2_struct_0(A_221))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.02/1.56  tff(c_2, plain, (![B_3, A_1]: (v1_xboole_0(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.02/1.56  tff(c_77, plain, (![A_221]: (v1_xboole_0('#skF_1'(A_221)) | ~v1_xboole_0(u1_struct_0(A_221)) | ~l1_pre_topc(A_221) | ~v2_pre_topc(A_221) | v2_struct_0(A_221))), inference(resolution, [status(thm)], [c_73, c_2])).
% 3.02/1.56  tff(c_93, plain, (v1_xboole_0('#skF_1'('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_90, c_77])).
% 3.02/1.56  tff(c_96, plain, (v1_xboole_0('#skF_1'('#skF_5')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_93])).
% 3.02/1.56  tff(c_97, plain, (v1_xboole_0('#skF_1'('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_46, c_96])).
% 3.02/1.56  tff(c_10, plain, (![A_8]: (~v1_xboole_0('#skF_1'(A_8)) | ~l1_pre_topc(A_8) | ~v2_pre_topc(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.02/1.56  tff(c_100, plain, (~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_97, c_10])).
% 3.02/1.56  tff(c_103, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_100])).
% 3.02/1.56  tff(c_105, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_103])).
% 3.02/1.56  tff(c_106, plain, (![D_226]: (m1_subset_1(k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', D_226), u1_struct_0('#skF_3')) | ~m1_subset_1(D_226, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_86])).
% 3.02/1.56  tff(c_58, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_189])).
% 3.02/1.56  tff(c_50, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_189])).
% 3.02/1.56  tff(c_48, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_189])).
% 3.02/1.56  tff(c_56, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_189])).
% 3.02/1.56  tff(c_54, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_189])).
% 3.02/1.56  tff(c_34, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_189])).
% 3.02/1.56  tff(c_32, plain, (v1_funct_2('#skF_7', u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_189])).
% 3.02/1.56  tff(c_30, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_189])).
% 3.02/1.56  tff(c_26, plain, (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_189])).
% 3.02/1.56  tff(c_162, plain, (![C_244, E_239, B_243, F_240, A_242, D_241]: (r1_tmap_1(B_243, A_242, k1_partfun1(u1_struct_0(B_243), u1_struct_0(C_244), u1_struct_0(C_244), u1_struct_0(A_242), D_241, E_239), F_240) | ~r1_tmap_1(C_244, A_242, E_239, k3_funct_2(u1_struct_0(B_243), u1_struct_0(C_244), D_241, F_240)) | ~r1_tmap_1(B_243, C_244, D_241, F_240) | ~m1_subset_1(k3_funct_2(u1_struct_0(B_243), u1_struct_0(C_244), D_241, F_240), u1_struct_0(C_244)) | ~m1_subset_1(F_240, u1_struct_0(B_243)) | ~m1_subset_1(E_239, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_244), u1_struct_0(A_242)))) | ~v1_funct_2(E_239, u1_struct_0(C_244), u1_struct_0(A_242)) | ~v1_funct_1(E_239) | ~m1_subset_1(D_241, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_243), u1_struct_0(C_244)))) | ~v1_funct_2(D_241, u1_struct_0(B_243), u1_struct_0(C_244)) | ~v1_funct_1(D_241) | ~l1_pre_topc(C_244) | ~v2_pre_topc(C_244) | v2_struct_0(C_244) | ~l1_pre_topc(B_243) | ~v2_pre_topc(B_243) | v2_struct_0(B_243) | ~l1_pre_topc(A_242) | ~v2_pre_topc(A_242) | v2_struct_0(A_242))), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.02/1.56  tff(c_22, plain, (~r1_tmap_1('#skF_5', '#skF_4', k1_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_6', '#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_189])).
% 3.02/1.56  tff(c_168, plain, (~r1_tmap_1('#skF_3', '#skF_4', '#skF_7', k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_8')) | ~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~m1_subset_1(k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_8'), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_162, c_22])).
% 3.02/1.56  tff(c_172, plain, (~r1_tmap_1('#skF_3', '#skF_4', '#skF_7', k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_8')) | ~m1_subset_1(k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_8'), u1_struct_0('#skF_3')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_44, c_42, c_56, c_54, c_40, c_38, c_36, c_34, c_32, c_30, c_28, c_26, c_168])).
% 3.02/1.56  tff(c_173, plain, (~r1_tmap_1('#skF_3', '#skF_4', '#skF_7', k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_8')) | ~m1_subset_1(k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_8'), u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_52, c_46, c_58, c_172])).
% 3.02/1.56  tff(c_174, plain, (~m1_subset_1(k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_8'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_173])).
% 3.02/1.56  tff(c_177, plain, (~m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_106, c_174])).
% 3.02/1.56  tff(c_181, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_177])).
% 3.02/1.56  tff(c_182, plain, (~r1_tmap_1('#skF_3', '#skF_4', '#skF_7', k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_8'))), inference(splitRight, [status(thm)], [c_173])).
% 3.02/1.56  tff(c_24, plain, (v5_pre_topc('#skF_7', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_189])).
% 3.02/1.56  tff(c_183, plain, (m1_subset_1(k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_8'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_173])).
% 3.02/1.56  tff(c_14, plain, (![B_22, A_10, C_28, D_31]: (r1_tmap_1(B_22, A_10, C_28, D_31) | ~m1_subset_1(D_31, u1_struct_0(B_22)) | ~v5_pre_topc(C_28, B_22, A_10) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_22), u1_struct_0(A_10)))) | ~v1_funct_2(C_28, u1_struct_0(B_22), u1_struct_0(A_10)) | ~v1_funct_1(C_28) | ~l1_pre_topc(B_22) | ~v2_pre_topc(B_22) | v2_struct_0(B_22) | ~l1_pre_topc(A_10) | ~v2_pre_topc(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.02/1.56  tff(c_185, plain, (![A_10, C_28]: (r1_tmap_1('#skF_3', A_10, C_28, k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_8')) | ~v5_pre_topc(C_28, '#skF_3', A_10) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(A_10)))) | ~v1_funct_2(C_28, u1_struct_0('#skF_3'), u1_struct_0(A_10)) | ~v1_funct_1(C_28) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_10) | ~v2_pre_topc(A_10) | v2_struct_0(A_10))), inference(resolution, [status(thm)], [c_183, c_14])).
% 3.02/1.56  tff(c_188, plain, (![A_10, C_28]: (r1_tmap_1('#skF_3', A_10, C_28, k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_8')) | ~v5_pre_topc(C_28, '#skF_3', A_10) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(A_10)))) | ~v1_funct_2(C_28, u1_struct_0('#skF_3'), u1_struct_0(A_10)) | ~v1_funct_1(C_28) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_10) | ~v2_pre_topc(A_10) | v2_struct_0(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_185])).
% 3.02/1.56  tff(c_198, plain, (![A_247, C_248]: (r1_tmap_1('#skF_3', A_247, C_248, k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_8')) | ~v5_pre_topc(C_248, '#skF_3', A_247) | ~m1_subset_1(C_248, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(A_247)))) | ~v1_funct_2(C_248, u1_struct_0('#skF_3'), u1_struct_0(A_247)) | ~v1_funct_1(C_248) | ~l1_pre_topc(A_247) | ~v2_pre_topc(A_247) | v2_struct_0(A_247))), inference(negUnitSimplification, [status(thm)], [c_58, c_188])).
% 3.02/1.56  tff(c_201, plain, (r1_tmap_1('#skF_3', '#skF_4', '#skF_7', k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_8')) | ~v5_pre_topc('#skF_7', '#skF_3', '#skF_4') | ~v1_funct_2('#skF_7', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_7') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_30, c_198])).
% 3.02/1.56  tff(c_204, plain, (r1_tmap_1('#skF_3', '#skF_4', '#skF_7', k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_8')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_34, c_32, c_24, c_201])).
% 3.02/1.56  tff(c_206, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_182, c_204])).
% 3.02/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.56  
% 3.02/1.56  Inference rules
% 3.02/1.56  ----------------------
% 3.02/1.56  #Ref     : 0
% 3.02/1.56  #Sup     : 20
% 3.02/1.56  #Fact    : 0
% 3.02/1.56  #Define  : 0
% 3.02/1.56  #Split   : 6
% 3.02/1.56  #Chain   : 0
% 3.02/1.56  #Close   : 0
% 3.02/1.56  
% 3.02/1.56  Ordering : KBO
% 3.02/1.56  
% 3.02/1.56  Simplification rules
% 3.02/1.56  ----------------------
% 3.02/1.56  #Subsume      : 0
% 3.02/1.56  #Demod        : 59
% 3.02/1.56  #Tautology    : 2
% 3.02/1.56  #SimpNegUnit  : 13
% 3.02/1.56  #BackRed      : 0
% 3.02/1.56  
% 3.02/1.56  #Partial instantiations: 0
% 3.02/1.56  #Strategies tried      : 1
% 3.02/1.56  
% 3.02/1.56  Timing (in seconds)
% 3.02/1.56  ----------------------
% 3.02/1.56  Preprocessing        : 0.45
% 3.02/1.56  Parsing              : 0.24
% 3.02/1.56  CNF conversion       : 0.06
% 3.02/1.56  Main loop            : 0.27
% 3.02/1.56  Inferencing          : 0.10
% 3.02/1.56  Reduction            : 0.09
% 3.02/1.56  Demodulation         : 0.06
% 3.02/1.56  BG Simplification    : 0.03
% 3.02/1.56  Subsumption          : 0.04
% 3.02/1.56  Abstraction          : 0.01
% 3.02/1.56  MUC search           : 0.00
% 3.02/1.56  Cooper               : 0.00
% 3.02/1.56  Total                : 0.76
% 3.02/1.56  Index Insertion      : 0.00
% 3.02/1.56  Index Deletion       : 0.00
% 3.02/1.56  Index Matching       : 0.00
% 3.02/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
