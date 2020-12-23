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
% DateTime   : Thu Dec  3 10:26:49 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 231 expanded)
%              Number of leaves         :   32 ( 112 expanded)
%              Depth                    :   11
%              Number of atoms          :  232 (1894 expanded)
%              Number of equality atoms :    1 (   3 expanded)
%              Maximal formula depth    :   27 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v5_pre_topc > v1_funct_2 > v4_pre_topc > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k1_partfun1 > k3_funct_2 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(f_187,negated_conjecture,(
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

tff(f_60,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc7_pre_topc)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_140,axiom,(
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

tff(f_89,axiom,(
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

tff(c_50,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_26,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_42,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_40,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_38,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_36,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_34,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_76,plain,(
    ! [A_222,B_223,C_224,D_225] :
      ( m1_subset_1(k3_funct_2(A_222,B_223,C_224,D_225),B_223)
      | ~ m1_subset_1(D_225,A_222)
      | ~ m1_subset_1(C_224,k1_zfmisc_1(k2_zfmisc_1(A_222,B_223)))
      | ~ v1_funct_2(C_224,A_222,B_223)
      | ~ v1_funct_1(C_224)
      | v1_xboole_0(A_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_78,plain,(
    ! [D_225] :
      ( m1_subset_1(k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',D_225),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(D_225,u1_struct_0('#skF_5'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0(u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_34,c_76])).

tff(c_83,plain,(
    ! [D_225] :
      ( m1_subset_1(k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',D_225),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(D_225,u1_struct_0('#skF_5'))
      | v1_xboole_0(u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_78])).

tff(c_87,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_70,plain,(
    ! [A_220] :
      ( m1_subset_1('#skF_1'(A_220),k1_zfmisc_1(u1_struct_0(A_220)))
      | ~ l1_pre_topc(A_220)
      | ~ v2_pre_topc(A_220)
      | v2_struct_0(A_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_xboole_0(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_74,plain,(
    ! [A_220] :
      ( v1_xboole_0('#skF_1'(A_220))
      | ~ v1_xboole_0(u1_struct_0(A_220))
      | ~ l1_pre_topc(A_220)
      | ~ v2_pre_topc(A_220)
      | v2_struct_0(A_220) ) ),
    inference(resolution,[status(thm)],[c_70,c_2])).

tff(c_90,plain,
    ( v1_xboole_0('#skF_1'('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_87,c_74])).

tff(c_93,plain,
    ( v1_xboole_0('#skF_1'('#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_90])).

tff(c_94,plain,(
    v1_xboole_0('#skF_1'('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_93])).

tff(c_8,plain,(
    ! [A_8] :
      ( ~ v1_xboole_0('#skF_1'(A_8))
      | ~ l1_pre_topc(A_8)
      | ~ v2_pre_topc(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_97,plain,
    ( ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_94,c_8])).

tff(c_100,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_97])).

tff(c_102,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_100])).

tff(c_103,plain,(
    ! [D_225] :
      ( m1_subset_1(k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',D_225),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(D_225,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_48,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_46,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_54,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_52,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_32,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_30,plain,(
    v1_funct_2('#skF_7',u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_28,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_24,plain,(
    r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_172,plain,(
    ! [F_242,E_241,B_245,A_244,D_243,C_246] :
      ( r1_tmap_1(B_245,A_244,k1_partfun1(u1_struct_0(B_245),u1_struct_0(C_246),u1_struct_0(C_246),u1_struct_0(A_244),D_243,E_241),F_242)
      | ~ r1_tmap_1(C_246,A_244,E_241,k3_funct_2(u1_struct_0(B_245),u1_struct_0(C_246),D_243,F_242))
      | ~ r1_tmap_1(B_245,C_246,D_243,F_242)
      | ~ m1_subset_1(k3_funct_2(u1_struct_0(B_245),u1_struct_0(C_246),D_243,F_242),u1_struct_0(C_246))
      | ~ m1_subset_1(F_242,u1_struct_0(B_245))
      | ~ m1_subset_1(E_241,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_246),u1_struct_0(A_244))))
      | ~ v1_funct_2(E_241,u1_struct_0(C_246),u1_struct_0(A_244))
      | ~ v1_funct_1(E_241)
      | ~ m1_subset_1(D_243,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_245),u1_struct_0(C_246))))
      | ~ v1_funct_2(D_243,u1_struct_0(B_245),u1_struct_0(C_246))
      | ~ v1_funct_1(D_243)
      | ~ l1_pre_topc(C_246)
      | ~ v2_pre_topc(C_246)
      | v2_struct_0(C_246)
      | ~ l1_pre_topc(B_245)
      | ~ v2_pre_topc(B_245)
      | v2_struct_0(B_245)
      | ~ l1_pre_topc(A_244)
      | ~ v2_pre_topc(A_244)
      | v2_struct_0(A_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_20,plain,(
    ~ r1_tmap_1('#skF_5','#skF_4',k1_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_6','#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_178,plain,
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
    inference(resolution,[status(thm)],[c_172,c_20])).

tff(c_182,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_4','#skF_7',k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_8'))
    | ~ m1_subset_1(k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_8'),u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_42,c_40,c_54,c_52,c_38,c_36,c_34,c_32,c_30,c_28,c_26,c_24,c_178])).

tff(c_183,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_4','#skF_7',k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_8'))
    | ~ m1_subset_1(k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_8'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_44,c_56,c_182])).

tff(c_184,plain,(
    ~ m1_subset_1(k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_8'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_183])).

tff(c_187,plain,(
    ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_103,c_184])).

tff(c_191,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_187])).

tff(c_192,plain,(
    ~ r1_tmap_1('#skF_3','#skF_4','#skF_7',k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_183])).

tff(c_22,plain,(
    v5_pre_topc('#skF_7','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_193,plain,(
    m1_subset_1(k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_8'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_183])).

tff(c_12,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_195,plain,(
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
    inference(resolution,[status(thm)],[c_193,c_12])).

tff(c_198,plain,(
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
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_195])).

tff(c_208,plain,(
    ! [A_249,C_250] :
      ( r1_tmap_1('#skF_3',A_249,C_250,k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_8'))
      | ~ v5_pre_topc(C_250,'#skF_3',A_249)
      | ~ m1_subset_1(C_250,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(A_249))))
      | ~ v1_funct_2(C_250,u1_struct_0('#skF_3'),u1_struct_0(A_249))
      | ~ v1_funct_1(C_250)
      | ~ l1_pre_topc(A_249)
      | ~ v2_pre_topc(A_249)
      | v2_struct_0(A_249) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_198])).

tff(c_211,plain,
    ( r1_tmap_1('#skF_3','#skF_4','#skF_7',k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_8'))
    | ~ v5_pre_topc('#skF_7','#skF_3','#skF_4')
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_7')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_208])).

tff(c_214,plain,
    ( r1_tmap_1('#skF_3','#skF_4','#skF_7',k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_8'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_32,c_30,c_22,c_211])).

tff(c_216,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_192,c_214])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:04:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.26/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.33  
% 2.26/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.33  %$ r1_tmap_1 > v5_pre_topc > v1_funct_2 > v4_pre_topc > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k1_partfun1 > k3_funct_2 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_8 > #skF_4
% 2.68/1.33  
% 2.68/1.33  %Foreground sorts:
% 2.68/1.33  
% 2.68/1.33  
% 2.68/1.33  %Background operators:
% 2.68/1.33  
% 2.68/1.33  
% 2.68/1.33  %Foreground operators:
% 2.68/1.33  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.68/1.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.68/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.68/1.33  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.68/1.33  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 2.68/1.33  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.68/1.33  tff('#skF_7', type, '#skF_7': $i).
% 2.68/1.33  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.68/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.68/1.33  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.68/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.68/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.68/1.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.68/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.68/1.33  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.68/1.33  tff('#skF_8', type, '#skF_8': $i).
% 2.68/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.68/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.68/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.68/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.68/1.33  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 2.68/1.33  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.68/1.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.68/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.68/1.33  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.68/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.68/1.33  
% 2.68/1.35  tff(f_187, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((~v2_struct_0(C) & v2_pre_topc(C)) & l1_pre_topc(C)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(C), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(A))))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => ((r1_tmap_1(C, A, D, F) & v5_pre_topc(E, A, B)) => r1_tmap_1(C, B, k1_partfun1(u1_struct_0(C), u1_struct_0(A), u1_struct_0(A), u1_struct_0(B), D, E), F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_tmap_1)).
% 2.68/1.35  tff(f_45, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => m1_subset_1(k3_funct_2(A, B, C, D), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_funct_2)).
% 2.68/1.35  tff(f_60, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: ((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc7_pre_topc)).
% 2.68/1.35  tff(f_32, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.68/1.35  tff(f_140, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((~v2_struct_0(C) & v2_pre_topc(C)) & l1_pre_topc(C)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(C))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(C))))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(A))))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((((G = k3_funct_2(u1_struct_0(B), u1_struct_0(C), D, F)) & r1_tmap_1(B, C, D, F)) & r1_tmap_1(C, A, E, G)) => r1_tmap_1(B, A, k1_partfun1(u1_struct_0(B), u1_struct_0(C), u1_struct_0(C), u1_struct_0(A), D, E), F)))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_tmap_1)).
% 2.68/1.35  tff(f_89, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (v5_pre_topc(C, B, A) <=> (![D]: (m1_subset_1(D, u1_struct_0(B)) => r1_tmap_1(B, A, C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_tmap_1)).
% 2.68/1.35  tff(c_50, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_187])).
% 2.68/1.35  tff(c_26, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_187])).
% 2.68/1.35  tff(c_44, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_187])).
% 2.68/1.35  tff(c_42, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_187])).
% 2.68/1.35  tff(c_40, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_187])).
% 2.68/1.35  tff(c_38, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_187])).
% 2.68/1.35  tff(c_36, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_187])).
% 2.68/1.35  tff(c_34, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_187])).
% 2.68/1.35  tff(c_76, plain, (![A_222, B_223, C_224, D_225]: (m1_subset_1(k3_funct_2(A_222, B_223, C_224, D_225), B_223) | ~m1_subset_1(D_225, A_222) | ~m1_subset_1(C_224, k1_zfmisc_1(k2_zfmisc_1(A_222, B_223))) | ~v1_funct_2(C_224, A_222, B_223) | ~v1_funct_1(C_224) | v1_xboole_0(A_222))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.68/1.35  tff(c_78, plain, (![D_225]: (m1_subset_1(k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', D_225), u1_struct_0('#skF_3')) | ~m1_subset_1(D_225, u1_struct_0('#skF_5')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | v1_xboole_0(u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_34, c_76])).
% 2.68/1.35  tff(c_83, plain, (![D_225]: (m1_subset_1(k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', D_225), u1_struct_0('#skF_3')) | ~m1_subset_1(D_225, u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_78])).
% 2.68/1.35  tff(c_87, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_83])).
% 2.68/1.35  tff(c_70, plain, (![A_220]: (m1_subset_1('#skF_1'(A_220), k1_zfmisc_1(u1_struct_0(A_220))) | ~l1_pre_topc(A_220) | ~v2_pre_topc(A_220) | v2_struct_0(A_220))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.68/1.35  tff(c_2, plain, (![B_3, A_1]: (v1_xboole_0(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.68/1.35  tff(c_74, plain, (![A_220]: (v1_xboole_0('#skF_1'(A_220)) | ~v1_xboole_0(u1_struct_0(A_220)) | ~l1_pre_topc(A_220) | ~v2_pre_topc(A_220) | v2_struct_0(A_220))), inference(resolution, [status(thm)], [c_70, c_2])).
% 2.68/1.35  tff(c_90, plain, (v1_xboole_0('#skF_1'('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_87, c_74])).
% 2.68/1.35  tff(c_93, plain, (v1_xboole_0('#skF_1'('#skF_5')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_90])).
% 2.68/1.35  tff(c_94, plain, (v1_xboole_0('#skF_1'('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_44, c_93])).
% 2.68/1.35  tff(c_8, plain, (![A_8]: (~v1_xboole_0('#skF_1'(A_8)) | ~l1_pre_topc(A_8) | ~v2_pre_topc(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.68/1.35  tff(c_97, plain, (~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_94, c_8])).
% 2.68/1.35  tff(c_100, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_97])).
% 2.68/1.35  tff(c_102, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_100])).
% 2.68/1.35  tff(c_103, plain, (![D_225]: (m1_subset_1(k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', D_225), u1_struct_0('#skF_3')) | ~m1_subset_1(D_225, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_83])).
% 2.68/1.35  tff(c_56, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_187])).
% 2.68/1.35  tff(c_48, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_187])).
% 2.68/1.35  tff(c_46, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_187])).
% 2.68/1.35  tff(c_54, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_187])).
% 2.68/1.35  tff(c_52, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_187])).
% 2.68/1.35  tff(c_32, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_187])).
% 2.68/1.35  tff(c_30, plain, (v1_funct_2('#skF_7', u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_187])).
% 2.68/1.35  tff(c_28, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_187])).
% 2.68/1.35  tff(c_24, plain, (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_187])).
% 2.68/1.35  tff(c_172, plain, (![F_242, E_241, B_245, A_244, D_243, C_246]: (r1_tmap_1(B_245, A_244, k1_partfun1(u1_struct_0(B_245), u1_struct_0(C_246), u1_struct_0(C_246), u1_struct_0(A_244), D_243, E_241), F_242) | ~r1_tmap_1(C_246, A_244, E_241, k3_funct_2(u1_struct_0(B_245), u1_struct_0(C_246), D_243, F_242)) | ~r1_tmap_1(B_245, C_246, D_243, F_242) | ~m1_subset_1(k3_funct_2(u1_struct_0(B_245), u1_struct_0(C_246), D_243, F_242), u1_struct_0(C_246)) | ~m1_subset_1(F_242, u1_struct_0(B_245)) | ~m1_subset_1(E_241, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_246), u1_struct_0(A_244)))) | ~v1_funct_2(E_241, u1_struct_0(C_246), u1_struct_0(A_244)) | ~v1_funct_1(E_241) | ~m1_subset_1(D_243, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_245), u1_struct_0(C_246)))) | ~v1_funct_2(D_243, u1_struct_0(B_245), u1_struct_0(C_246)) | ~v1_funct_1(D_243) | ~l1_pre_topc(C_246) | ~v2_pre_topc(C_246) | v2_struct_0(C_246) | ~l1_pre_topc(B_245) | ~v2_pre_topc(B_245) | v2_struct_0(B_245) | ~l1_pre_topc(A_244) | ~v2_pre_topc(A_244) | v2_struct_0(A_244))), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.68/1.35  tff(c_20, plain, (~r1_tmap_1('#skF_5', '#skF_4', k1_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_6', '#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_187])).
% 2.68/1.35  tff(c_178, plain, (~r1_tmap_1('#skF_3', '#skF_4', '#skF_7', k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_8')) | ~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~m1_subset_1(k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_8'), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_172, c_20])).
% 2.68/1.35  tff(c_182, plain, (~r1_tmap_1('#skF_3', '#skF_4', '#skF_7', k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_8')) | ~m1_subset_1(k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_8'), u1_struct_0('#skF_3')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_42, c_40, c_54, c_52, c_38, c_36, c_34, c_32, c_30, c_28, c_26, c_24, c_178])).
% 2.68/1.35  tff(c_183, plain, (~r1_tmap_1('#skF_3', '#skF_4', '#skF_7', k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_8')) | ~m1_subset_1(k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_8'), u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_50, c_44, c_56, c_182])).
% 2.68/1.35  tff(c_184, plain, (~m1_subset_1(k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_8'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_183])).
% 2.68/1.35  tff(c_187, plain, (~m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_103, c_184])).
% 2.68/1.35  tff(c_191, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_187])).
% 2.68/1.35  tff(c_192, plain, (~r1_tmap_1('#skF_3', '#skF_4', '#skF_7', k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_8'))), inference(splitRight, [status(thm)], [c_183])).
% 2.68/1.35  tff(c_22, plain, (v5_pre_topc('#skF_7', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_187])).
% 2.68/1.35  tff(c_193, plain, (m1_subset_1(k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_8'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_183])).
% 2.68/1.35  tff(c_12, plain, (![B_22, A_10, C_28, D_31]: (r1_tmap_1(B_22, A_10, C_28, D_31) | ~m1_subset_1(D_31, u1_struct_0(B_22)) | ~v5_pre_topc(C_28, B_22, A_10) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_22), u1_struct_0(A_10)))) | ~v1_funct_2(C_28, u1_struct_0(B_22), u1_struct_0(A_10)) | ~v1_funct_1(C_28) | ~l1_pre_topc(B_22) | ~v2_pre_topc(B_22) | v2_struct_0(B_22) | ~l1_pre_topc(A_10) | ~v2_pre_topc(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.68/1.35  tff(c_195, plain, (![A_10, C_28]: (r1_tmap_1('#skF_3', A_10, C_28, k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_8')) | ~v5_pre_topc(C_28, '#skF_3', A_10) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(A_10)))) | ~v1_funct_2(C_28, u1_struct_0('#skF_3'), u1_struct_0(A_10)) | ~v1_funct_1(C_28) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_10) | ~v2_pre_topc(A_10) | v2_struct_0(A_10))), inference(resolution, [status(thm)], [c_193, c_12])).
% 2.68/1.35  tff(c_198, plain, (![A_10, C_28]: (r1_tmap_1('#skF_3', A_10, C_28, k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_8')) | ~v5_pre_topc(C_28, '#skF_3', A_10) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(A_10)))) | ~v1_funct_2(C_28, u1_struct_0('#skF_3'), u1_struct_0(A_10)) | ~v1_funct_1(C_28) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_10) | ~v2_pre_topc(A_10) | v2_struct_0(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_195])).
% 2.68/1.35  tff(c_208, plain, (![A_249, C_250]: (r1_tmap_1('#skF_3', A_249, C_250, k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_8')) | ~v5_pre_topc(C_250, '#skF_3', A_249) | ~m1_subset_1(C_250, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(A_249)))) | ~v1_funct_2(C_250, u1_struct_0('#skF_3'), u1_struct_0(A_249)) | ~v1_funct_1(C_250) | ~l1_pre_topc(A_249) | ~v2_pre_topc(A_249) | v2_struct_0(A_249))), inference(negUnitSimplification, [status(thm)], [c_56, c_198])).
% 2.68/1.35  tff(c_211, plain, (r1_tmap_1('#skF_3', '#skF_4', '#skF_7', k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_8')) | ~v5_pre_topc('#skF_7', '#skF_3', '#skF_4') | ~v1_funct_2('#skF_7', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_7') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_28, c_208])).
% 2.68/1.35  tff(c_214, plain, (r1_tmap_1('#skF_3', '#skF_4', '#skF_7', k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_8')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_32, c_30, c_22, c_211])).
% 2.68/1.35  tff(c_216, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_192, c_214])).
% 2.68/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.35  
% 2.68/1.35  Inference rules
% 2.68/1.35  ----------------------
% 2.68/1.35  #Ref     : 0
% 2.68/1.35  #Sup     : 22
% 2.68/1.35  #Fact    : 0
% 2.68/1.35  #Define  : 0
% 2.68/1.35  #Split   : 6
% 2.68/1.35  #Chain   : 0
% 2.68/1.35  #Close   : 0
% 2.68/1.35  
% 2.68/1.35  Ordering : KBO
% 2.68/1.35  
% 2.68/1.35  Simplification rules
% 2.68/1.35  ----------------------
% 2.68/1.35  #Subsume      : 0
% 2.68/1.35  #Demod        : 72
% 2.68/1.35  #Tautology    : 3
% 2.68/1.35  #SimpNegUnit  : 15
% 2.68/1.35  #BackRed      : 0
% 2.68/1.35  
% 2.68/1.35  #Partial instantiations: 0
% 2.68/1.35  #Strategies tried      : 1
% 2.68/1.35  
% 2.68/1.35  Timing (in seconds)
% 2.68/1.35  ----------------------
% 2.68/1.35  Preprocessing        : 0.35
% 2.68/1.35  Parsing              : 0.17
% 2.68/1.35  CNF conversion       : 0.05
% 2.68/1.36  Main loop            : 0.24
% 2.68/1.36  Inferencing          : 0.09
% 2.68/1.36  Reduction            : 0.08
% 2.68/1.36  Demodulation         : 0.06
% 2.68/1.36  BG Simplification    : 0.02
% 2.68/1.36  Subsumption          : 0.04
% 2.68/1.36  Abstraction          : 0.01
% 2.68/1.36  MUC search           : 0.00
% 2.68/1.36  Cooper               : 0.00
% 2.68/1.36  Total                : 0.63
% 2.68/1.36  Index Insertion      : 0.00
% 2.68/1.36  Index Deletion       : 0.00
% 2.68/1.36  Index Matching       : 0.00
% 2.68/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
