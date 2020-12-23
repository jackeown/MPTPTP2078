%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:11 EST 2020

% Result     : Theorem 3.52s
% Output     : CNFRefutation 3.52s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 227 expanded)
%              Number of leaves         :   29 ( 108 expanded)
%              Depth                    :   13
%              Number of atoms          :  392 (2428 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   28 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > r4_tsep_1 > v1_borsuk_1 > r1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k10_tmap_1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k10_tmap_1,type,(
    k10_tmap_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_tsep_1,type,(
    k1_tsep_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r4_tsep_1,type,(
    r4_tsep_1: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v1_borsuk_1,type,(
    v1_borsuk_1: ( $i * $i ) > $o )).

tff(f_203,negated_conjecture,(
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
                  & v1_borsuk_1(C,A)
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & v1_borsuk_1(D,A)
                      & m1_pre_topc(D,A) )
                   => ( r1_tsep_1(C,D)
                     => ! [E] :
                          ( ( v1_funct_1(E)
                            & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                            & v5_pre_topc(E,C,B)
                            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                         => ! [F] :
                              ( ( v1_funct_1(F)
                                & v1_funct_2(F,u1_struct_0(D),u1_struct_0(B))
                                & v5_pre_topc(F,D,B)
                                & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                             => ( v1_funct_1(k10_tmap_1(A,B,C,D,E,F))
                                & v1_funct_2(k10_tmap_1(A,B,C,D,E,F),u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B))
                                & v5_pre_topc(k10_tmap_1(A,B,C,D,E,F),k1_tsep_1(A,C,D),B)
                                & m1_subset_1(k10_tmap_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B)))) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_tmap_1)).

tff(f_143,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_borsuk_1(B,A)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( v1_borsuk_1(C,A)
                & m1_pre_topc(C,A) )
             => r4_tsep_1(A,B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_tsep_1)).

tff(f_124,axiom,(
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
                & m1_pre_topc(C,A) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,A) )
                 => ( r1_tsep_1(C,D)
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                          & v5_pre_topc(E,C,B)
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                       => ! [F] :
                            ( ( v1_funct_1(F)
                              & v1_funct_2(F,u1_struct_0(D),u1_struct_0(B))
                              & v5_pre_topc(F,D,B)
                              & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                           => ( r4_tsep_1(A,C,D)
                             => ( v1_funct_1(k10_tmap_1(A,B,C,D,E,F))
                                & v1_funct_2(k10_tmap_1(A,B,C,D,E,F),u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B))
                                & v5_pre_topc(k10_tmap_1(A,B,C,D,E,F),k1_tsep_1(A,C,D),B)
                                & m1_subset_1(k10_tmap_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B)))) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_tmap_1)).

tff(f_67,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & v2_pre_topc(B)
        & l1_pre_topc(B)
        & ~ v2_struct_0(C)
        & m1_pre_topc(C,A)
        & ~ v2_struct_0(D)
        & m1_pre_topc(D,A)
        & v1_funct_1(E)
        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B))))
        & v1_funct_1(F)
        & v1_funct_2(F,u1_struct_0(D),u1_struct_0(B))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
     => ( v1_funct_1(k10_tmap_1(A,B,C,D,E,F))
        & v1_funct_2(k10_tmap_1(A,B,C,D,E,F),u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B))
        & m1_subset_1(k10_tmap_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_tmap_1)).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_58,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_56,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_46,plain,(
    v1_borsuk_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_44,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_40,plain,(
    v1_borsuk_1('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_38,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_16,plain,(
    ! [A_70,B_74,C_76] :
      ( r4_tsep_1(A_70,B_74,C_76)
      | ~ m1_pre_topc(C_76,A_70)
      | ~ v1_borsuk_1(C_76,A_70)
      | ~ m1_pre_topc(B_74,A_70)
      | ~ v1_borsuk_1(B_74,A_70)
      | ~ l1_pre_topc(A_70)
      | ~ v2_pre_topc(A_70)
      | v2_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_36,plain,(
    r1_tsep_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_34,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_32,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_30,plain,(
    v5_pre_topc('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_28,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_52,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_50,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_26,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_24,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_22,plain,(
    v5_pre_topc('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_20,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_286,plain,(
    ! [A_225,D_226,E_222,F_227,C_223,B_224] :
      ( v5_pre_topc(k10_tmap_1(A_225,B_224,C_223,D_226,E_222,F_227),k1_tsep_1(A_225,C_223,D_226),B_224)
      | ~ r4_tsep_1(A_225,C_223,D_226)
      | ~ m1_subset_1(F_227,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_226),u1_struct_0(B_224))))
      | ~ v5_pre_topc(F_227,D_226,B_224)
      | ~ v1_funct_2(F_227,u1_struct_0(D_226),u1_struct_0(B_224))
      | ~ v1_funct_1(F_227)
      | ~ m1_subset_1(E_222,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_223),u1_struct_0(B_224))))
      | ~ v5_pre_topc(E_222,C_223,B_224)
      | ~ v1_funct_2(E_222,u1_struct_0(C_223),u1_struct_0(B_224))
      | ~ v1_funct_1(E_222)
      | ~ r1_tsep_1(C_223,D_226)
      | ~ m1_pre_topc(D_226,A_225)
      | v2_struct_0(D_226)
      | ~ m1_pre_topc(C_223,A_225)
      | v2_struct_0(C_223)
      | ~ l1_pre_topc(B_224)
      | ~ v2_pre_topc(B_224)
      | v2_struct_0(B_224)
      | ~ l1_pre_topc(A_225)
      | ~ v2_pre_topc(A_225)
      | v2_struct_0(A_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_292,plain,(
    ! [A_225,C_223,E_222] :
      ( v5_pre_topc(k10_tmap_1(A_225,'#skF_2',C_223,'#skF_4',E_222,'#skF_6'),k1_tsep_1(A_225,C_223,'#skF_4'),'#skF_2')
      | ~ r4_tsep_1(A_225,C_223,'#skF_4')
      | ~ v5_pre_topc('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_222,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_223),u1_struct_0('#skF_2'))))
      | ~ v5_pre_topc(E_222,C_223,'#skF_2')
      | ~ v1_funct_2(E_222,u1_struct_0(C_223),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_222)
      | ~ r1_tsep_1(C_223,'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_225)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_223,A_225)
      | v2_struct_0(C_223)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_225)
      | ~ v2_pre_topc(A_225)
      | v2_struct_0(A_225) ) ),
    inference(resolution,[status(thm)],[c_20,c_286])).

tff(c_302,plain,(
    ! [A_225,C_223,E_222] :
      ( v5_pre_topc(k10_tmap_1(A_225,'#skF_2',C_223,'#skF_4',E_222,'#skF_6'),k1_tsep_1(A_225,C_223,'#skF_4'),'#skF_2')
      | ~ r4_tsep_1(A_225,C_223,'#skF_4')
      | ~ m1_subset_1(E_222,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_223),u1_struct_0('#skF_2'))))
      | ~ v5_pre_topc(E_222,C_223,'#skF_2')
      | ~ v1_funct_2(E_222,u1_struct_0(C_223),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_222)
      | ~ r1_tsep_1(C_223,'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_225)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_223,A_225)
      | v2_struct_0(C_223)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_225)
      | ~ v2_pre_topc(A_225)
      | v2_struct_0(A_225) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_26,c_24,c_22,c_292])).

tff(c_308,plain,(
    ! [A_228,C_229,E_230] :
      ( v5_pre_topc(k10_tmap_1(A_228,'#skF_2',C_229,'#skF_4',E_230,'#skF_6'),k1_tsep_1(A_228,C_229,'#skF_4'),'#skF_2')
      | ~ r4_tsep_1(A_228,C_229,'#skF_4')
      | ~ m1_subset_1(E_230,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_229),u1_struct_0('#skF_2'))))
      | ~ v5_pre_topc(E_230,C_229,'#skF_2')
      | ~ v1_funct_2(E_230,u1_struct_0(C_229),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_230)
      | ~ r1_tsep_1(C_229,'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_228)
      | ~ m1_pre_topc(C_229,A_228)
      | v2_struct_0(C_229)
      | ~ l1_pre_topc(A_228)
      | ~ v2_pre_topc(A_228)
      | v2_struct_0(A_228) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_42,c_302])).

tff(c_317,plain,(
    ! [A_228] :
      ( v5_pre_topc(k10_tmap_1(A_228,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1(A_228,'#skF_3','#skF_4'),'#skF_2')
      | ~ r4_tsep_1(A_228,'#skF_3','#skF_4')
      | ~ v5_pre_topc('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ r1_tsep_1('#skF_3','#skF_4')
      | ~ m1_pre_topc('#skF_4',A_228)
      | ~ m1_pre_topc('#skF_3',A_228)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_228)
      | ~ v2_pre_topc(A_228)
      | v2_struct_0(A_228) ) ),
    inference(resolution,[status(thm)],[c_28,c_308])).

tff(c_331,plain,(
    ! [A_228] :
      ( v5_pre_topc(k10_tmap_1(A_228,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1(A_228,'#skF_3','#skF_4'),'#skF_2')
      | ~ r4_tsep_1(A_228,'#skF_3','#skF_4')
      | ~ m1_pre_topc('#skF_4',A_228)
      | ~ m1_pre_topc('#skF_3',A_228)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_228)
      | ~ v2_pre_topc(A_228)
      | v2_struct_0(A_228) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_30,c_317])).

tff(c_334,plain,(
    ! [A_231] :
      ( v5_pre_topc(k10_tmap_1(A_231,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1(A_231,'#skF_3','#skF_4'),'#skF_2')
      | ~ r4_tsep_1(A_231,'#skF_3','#skF_4')
      | ~ m1_pre_topc('#skF_4',A_231)
      | ~ m1_pre_topc('#skF_3',A_231)
      | ~ l1_pre_topc(A_231)
      | ~ v2_pre_topc(A_231)
      | v2_struct_0(A_231) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_331])).

tff(c_195,plain,(
    ! [B_191,A_193,F_188,E_189,D_190,C_192] :
      ( v1_funct_2(k10_tmap_1(A_193,B_191,C_192,D_190,E_189,F_188),u1_struct_0(k1_tsep_1(A_193,C_192,D_190)),u1_struct_0(B_191))
      | ~ m1_subset_1(F_188,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_190),u1_struct_0(B_191))))
      | ~ v1_funct_2(F_188,u1_struct_0(D_190),u1_struct_0(B_191))
      | ~ v1_funct_1(F_188)
      | ~ m1_subset_1(E_189,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_192),u1_struct_0(B_191))))
      | ~ v1_funct_2(E_189,u1_struct_0(C_192),u1_struct_0(B_191))
      | ~ v1_funct_1(E_189)
      | ~ m1_pre_topc(D_190,A_193)
      | v2_struct_0(D_190)
      | ~ m1_pre_topc(C_192,A_193)
      | v2_struct_0(C_192)
      | ~ l1_pre_topc(B_191)
      | ~ v2_pre_topc(B_191)
      | v2_struct_0(B_191)
      | ~ l1_pre_topc(A_193)
      | ~ v2_pre_topc(A_193)
      | v2_struct_0(A_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_147,plain,(
    ! [A_181,E_177,C_180,B_179,D_178,F_176] :
      ( m1_subset_1(k10_tmap_1(A_181,B_179,C_180,D_178,E_177,F_176),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_181,C_180,D_178)),u1_struct_0(B_179))))
      | ~ m1_subset_1(F_176,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_178),u1_struct_0(B_179))))
      | ~ v1_funct_2(F_176,u1_struct_0(D_178),u1_struct_0(B_179))
      | ~ v1_funct_1(F_176)
      | ~ m1_subset_1(E_177,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_180),u1_struct_0(B_179))))
      | ~ v1_funct_2(E_177,u1_struct_0(C_180),u1_struct_0(B_179))
      | ~ v1_funct_1(E_177)
      | ~ m1_pre_topc(D_178,A_181)
      | v2_struct_0(D_178)
      | ~ m1_pre_topc(C_180,A_181)
      | v2_struct_0(C_180)
      | ~ l1_pre_topc(B_179)
      | ~ v2_pre_topc(B_179)
      | v2_struct_0(B_179)
      | ~ l1_pre_topc(A_181)
      | ~ v2_pre_topc(A_181)
      | v2_struct_0(A_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_63,plain,(
    ! [B_140,E_138,C_141,A_142,F_137,D_139] :
      ( v1_funct_1(k10_tmap_1(A_142,B_140,C_141,D_139,E_138,F_137))
      | ~ m1_subset_1(F_137,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_139),u1_struct_0(B_140))))
      | ~ v1_funct_2(F_137,u1_struct_0(D_139),u1_struct_0(B_140))
      | ~ v1_funct_1(F_137)
      | ~ m1_subset_1(E_138,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_141),u1_struct_0(B_140))))
      | ~ v1_funct_2(E_138,u1_struct_0(C_141),u1_struct_0(B_140))
      | ~ v1_funct_1(E_138)
      | ~ m1_pre_topc(D_139,A_142)
      | v2_struct_0(D_139)
      | ~ m1_pre_topc(C_141,A_142)
      | v2_struct_0(C_141)
      | ~ l1_pre_topc(B_140)
      | ~ v2_pre_topc(B_140)
      | v2_struct_0(B_140)
      | ~ l1_pre_topc(A_142)
      | ~ v2_pre_topc(A_142)
      | v2_struct_0(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_65,plain,(
    ! [A_142,C_141,E_138] :
      ( v1_funct_1(k10_tmap_1(A_142,'#skF_2',C_141,'#skF_4',E_138,'#skF_6'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_138,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_141),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_138,u1_struct_0(C_141),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_138)
      | ~ m1_pre_topc('#skF_4',A_142)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_141,A_142)
      | v2_struct_0(C_141)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_142)
      | ~ v2_pre_topc(A_142)
      | v2_struct_0(A_142) ) ),
    inference(resolution,[status(thm)],[c_20,c_63])).

tff(c_70,plain,(
    ! [A_142,C_141,E_138] :
      ( v1_funct_1(k10_tmap_1(A_142,'#skF_2',C_141,'#skF_4',E_138,'#skF_6'))
      | ~ m1_subset_1(E_138,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_141),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_138,u1_struct_0(C_141),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_138)
      | ~ m1_pre_topc('#skF_4',A_142)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_141,A_142)
      | v2_struct_0(C_141)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_142)
      | ~ v2_pre_topc(A_142)
      | v2_struct_0(A_142) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_26,c_24,c_65])).

tff(c_77,plain,(
    ! [A_149,C_150,E_151] :
      ( v1_funct_1(k10_tmap_1(A_149,'#skF_2',C_150,'#skF_4',E_151,'#skF_6'))
      | ~ m1_subset_1(E_151,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_150),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_151,u1_struct_0(C_150),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_151)
      | ~ m1_pre_topc('#skF_4',A_149)
      | ~ m1_pre_topc(C_150,A_149)
      | v2_struct_0(C_150)
      | ~ l1_pre_topc(A_149)
      | ~ v2_pre_topc(A_149)
      | v2_struct_0(A_149) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_42,c_70])).

tff(c_81,plain,(
    ! [A_149] :
      ( v1_funct_1(k10_tmap_1(A_149,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4',A_149)
      | ~ m1_pre_topc('#skF_3',A_149)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_149)
      | ~ v2_pre_topc(A_149)
      | v2_struct_0(A_149) ) ),
    inference(resolution,[status(thm)],[c_28,c_77])).

tff(c_88,plain,(
    ! [A_149] :
      ( v1_funct_1(k10_tmap_1(A_149,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc('#skF_4',A_149)
      | ~ m1_pre_topc('#skF_3',A_149)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_149)
      | ~ v2_pre_topc(A_149)
      | v2_struct_0(A_149) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_81])).

tff(c_91,plain,(
    ! [A_153] :
      ( v1_funct_1(k10_tmap_1(A_153,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc('#skF_4',A_153)
      | ~ m1_pre_topc('#skF_3',A_153)
      | ~ l1_pre_topc(A_153)
      | ~ v2_pre_topc(A_153)
      | v2_struct_0(A_153) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_88])).

tff(c_18,plain,
    ( ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_62,plain,(
    ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_94,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_91,c_62])).

tff(c_97,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_44,c_38,c_94])).

tff(c_99,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_97])).

tff(c_100,plain,
    ( ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
    | ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_102,plain,(
    ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_158,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_147,c_102])).

tff(c_170,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_50,c_44,c_38,c_34,c_32,c_28,c_26,c_24,c_20,c_158])).

tff(c_172,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_48,c_42,c_170])).

tff(c_173,plain,
    ( ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_175,plain,(
    ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_173])).

tff(c_198,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_195,c_175])).

tff(c_201,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_50,c_44,c_38,c_34,c_32,c_28,c_26,c_24,c_20,c_198])).

tff(c_203,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_48,c_42,c_201])).

tff(c_204,plain,(
    ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_173])).

tff(c_337,plain,
    ( ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_334,c_204])).

tff(c_340,plain,
    ( ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_44,c_38,c_337])).

tff(c_341,plain,(
    ~ r4_tsep_1('#skF_1','#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_340])).

tff(c_369,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ v1_borsuk_1('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ v1_borsuk_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_341])).

tff(c_372,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_46,c_44,c_40,c_38,c_369])).

tff(c_374,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_372])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:21:52 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.52/1.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.52/1.64  
% 3.52/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.52/1.64  %$ v5_pre_topc > v1_funct_2 > r4_tsep_1 > v1_borsuk_1 > r1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k10_tmap_1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.52/1.64  
% 3.52/1.64  %Foreground sorts:
% 3.52/1.64  
% 3.52/1.64  
% 3.52/1.64  %Background operators:
% 3.52/1.64  
% 3.52/1.64  
% 3.52/1.64  %Foreground operators:
% 3.52/1.64  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.52/1.64  tff(k10_tmap_1, type, k10_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.52/1.64  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 3.52/1.64  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.52/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.52/1.64  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.52/1.64  tff(r4_tsep_1, type, r4_tsep_1: ($i * $i * $i) > $o).
% 3.52/1.64  tff('#skF_5', type, '#skF_5': $i).
% 3.52/1.64  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.52/1.64  tff('#skF_6', type, '#skF_6': $i).
% 3.52/1.64  tff('#skF_2', type, '#skF_2': $i).
% 3.52/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.52/1.64  tff('#skF_1', type, '#skF_1': $i).
% 3.52/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.52/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.52/1.64  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.52/1.64  tff('#skF_4', type, '#skF_4': $i).
% 3.52/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.52/1.64  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 3.52/1.64  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.52/1.64  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.52/1.64  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 3.52/1.64  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.52/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.52/1.64  tff(v1_borsuk_1, type, v1_borsuk_1: ($i * $i) > $o).
% 3.52/1.64  
% 3.52/1.67  tff(f_203, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((~v2_struct_0(C) & v1_borsuk_1(C, A)) & m1_pre_topc(C, A)) => (![D]: (((~v2_struct_0(D) & v1_borsuk_1(D, A)) & m1_pre_topc(D, A)) => (r1_tsep_1(C, D) => (![E]: ((((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & v5_pre_topc(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: ((((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (((v1_funct_1(k10_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k10_tmap_1(A, B, C, D, E, F), u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & v5_pre_topc(k10_tmap_1(A, B, C, D, E, F), k1_tsep_1(A, C, D), B)) & m1_subset_1(k10_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_tmap_1)).
% 3.52/1.67  tff(f_143, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_borsuk_1(B, A) & m1_pre_topc(B, A)) => (![C]: ((v1_borsuk_1(C, A) & m1_pre_topc(C, A)) => r4_tsep_1(A, B, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_tsep_1)).
% 3.52/1.67  tff(f_124, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (r1_tsep_1(C, D) => (![E]: ((((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & v5_pre_topc(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: ((((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (r4_tsep_1(A, C, D) => (((v1_funct_1(k10_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k10_tmap_1(A, B, C, D, E, F), u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & v5_pre_topc(k10_tmap_1(A, B, C, D, E, F), k1_tsep_1(A, C, D), B)) & m1_subset_1(k10_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_tmap_1)).
% 3.52/1.67  tff(f_67, axiom, (![A, B, C, D, E, F]: ((((((((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) & ~v2_struct_0(D)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) & v1_funct_1(F)) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_funct_1(k10_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k10_tmap_1(A, B, C, D, E, F), u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & m1_subset_1(k10_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k10_tmap_1)).
% 3.52/1.67  tff(c_60, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_203])).
% 3.52/1.67  tff(c_58, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_203])).
% 3.52/1.67  tff(c_56, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_203])).
% 3.52/1.67  tff(c_46, plain, (v1_borsuk_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_203])).
% 3.52/1.67  tff(c_44, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_203])).
% 3.52/1.67  tff(c_40, plain, (v1_borsuk_1('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_203])).
% 3.52/1.67  tff(c_38, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_203])).
% 3.52/1.67  tff(c_16, plain, (![A_70, B_74, C_76]: (r4_tsep_1(A_70, B_74, C_76) | ~m1_pre_topc(C_76, A_70) | ~v1_borsuk_1(C_76, A_70) | ~m1_pre_topc(B_74, A_70) | ~v1_borsuk_1(B_74, A_70) | ~l1_pre_topc(A_70) | ~v2_pre_topc(A_70) | v2_struct_0(A_70))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.52/1.67  tff(c_48, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_203])).
% 3.52/1.67  tff(c_36, plain, (r1_tsep_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_203])).
% 3.52/1.67  tff(c_34, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_203])).
% 3.52/1.67  tff(c_32, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_203])).
% 3.52/1.67  tff(c_30, plain, (v5_pre_topc('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_203])).
% 3.52/1.67  tff(c_28, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_203])).
% 3.52/1.67  tff(c_54, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_203])).
% 3.52/1.67  tff(c_42, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_203])).
% 3.52/1.67  tff(c_52, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_203])).
% 3.52/1.67  tff(c_50, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_203])).
% 3.52/1.67  tff(c_26, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_203])).
% 3.52/1.67  tff(c_24, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_203])).
% 3.52/1.67  tff(c_22, plain, (v5_pre_topc('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_203])).
% 3.52/1.67  tff(c_20, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_203])).
% 3.52/1.67  tff(c_286, plain, (![A_225, D_226, E_222, F_227, C_223, B_224]: (v5_pre_topc(k10_tmap_1(A_225, B_224, C_223, D_226, E_222, F_227), k1_tsep_1(A_225, C_223, D_226), B_224) | ~r4_tsep_1(A_225, C_223, D_226) | ~m1_subset_1(F_227, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_226), u1_struct_0(B_224)))) | ~v5_pre_topc(F_227, D_226, B_224) | ~v1_funct_2(F_227, u1_struct_0(D_226), u1_struct_0(B_224)) | ~v1_funct_1(F_227) | ~m1_subset_1(E_222, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_223), u1_struct_0(B_224)))) | ~v5_pre_topc(E_222, C_223, B_224) | ~v1_funct_2(E_222, u1_struct_0(C_223), u1_struct_0(B_224)) | ~v1_funct_1(E_222) | ~r1_tsep_1(C_223, D_226) | ~m1_pre_topc(D_226, A_225) | v2_struct_0(D_226) | ~m1_pre_topc(C_223, A_225) | v2_struct_0(C_223) | ~l1_pre_topc(B_224) | ~v2_pre_topc(B_224) | v2_struct_0(B_224) | ~l1_pre_topc(A_225) | ~v2_pre_topc(A_225) | v2_struct_0(A_225))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.52/1.67  tff(c_292, plain, (![A_225, C_223, E_222]: (v5_pre_topc(k10_tmap_1(A_225, '#skF_2', C_223, '#skF_4', E_222, '#skF_6'), k1_tsep_1(A_225, C_223, '#skF_4'), '#skF_2') | ~r4_tsep_1(A_225, C_223, '#skF_4') | ~v5_pre_topc('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_222, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_223), u1_struct_0('#skF_2')))) | ~v5_pre_topc(E_222, C_223, '#skF_2') | ~v1_funct_2(E_222, u1_struct_0(C_223), u1_struct_0('#skF_2')) | ~v1_funct_1(E_222) | ~r1_tsep_1(C_223, '#skF_4') | ~m1_pre_topc('#skF_4', A_225) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_223, A_225) | v2_struct_0(C_223) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_225) | ~v2_pre_topc(A_225) | v2_struct_0(A_225))), inference(resolution, [status(thm)], [c_20, c_286])).
% 3.52/1.67  tff(c_302, plain, (![A_225, C_223, E_222]: (v5_pre_topc(k10_tmap_1(A_225, '#skF_2', C_223, '#skF_4', E_222, '#skF_6'), k1_tsep_1(A_225, C_223, '#skF_4'), '#skF_2') | ~r4_tsep_1(A_225, C_223, '#skF_4') | ~m1_subset_1(E_222, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_223), u1_struct_0('#skF_2')))) | ~v5_pre_topc(E_222, C_223, '#skF_2') | ~v1_funct_2(E_222, u1_struct_0(C_223), u1_struct_0('#skF_2')) | ~v1_funct_1(E_222) | ~r1_tsep_1(C_223, '#skF_4') | ~m1_pre_topc('#skF_4', A_225) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_223, A_225) | v2_struct_0(C_223) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_225) | ~v2_pre_topc(A_225) | v2_struct_0(A_225))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_26, c_24, c_22, c_292])).
% 3.52/1.67  tff(c_308, plain, (![A_228, C_229, E_230]: (v5_pre_topc(k10_tmap_1(A_228, '#skF_2', C_229, '#skF_4', E_230, '#skF_6'), k1_tsep_1(A_228, C_229, '#skF_4'), '#skF_2') | ~r4_tsep_1(A_228, C_229, '#skF_4') | ~m1_subset_1(E_230, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_229), u1_struct_0('#skF_2')))) | ~v5_pre_topc(E_230, C_229, '#skF_2') | ~v1_funct_2(E_230, u1_struct_0(C_229), u1_struct_0('#skF_2')) | ~v1_funct_1(E_230) | ~r1_tsep_1(C_229, '#skF_4') | ~m1_pre_topc('#skF_4', A_228) | ~m1_pre_topc(C_229, A_228) | v2_struct_0(C_229) | ~l1_pre_topc(A_228) | ~v2_pre_topc(A_228) | v2_struct_0(A_228))), inference(negUnitSimplification, [status(thm)], [c_54, c_42, c_302])).
% 3.52/1.67  tff(c_317, plain, (![A_228]: (v5_pre_topc(k10_tmap_1(A_228, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_tsep_1(A_228, '#skF_3', '#skF_4'), '#skF_2') | ~r4_tsep_1(A_228, '#skF_3', '#skF_4') | ~v5_pre_topc('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~r1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', A_228) | ~m1_pre_topc('#skF_3', A_228) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_228) | ~v2_pre_topc(A_228) | v2_struct_0(A_228))), inference(resolution, [status(thm)], [c_28, c_308])).
% 3.52/1.67  tff(c_331, plain, (![A_228]: (v5_pre_topc(k10_tmap_1(A_228, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_tsep_1(A_228, '#skF_3', '#skF_4'), '#skF_2') | ~r4_tsep_1(A_228, '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', A_228) | ~m1_pre_topc('#skF_3', A_228) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_228) | ~v2_pre_topc(A_228) | v2_struct_0(A_228))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_30, c_317])).
% 3.52/1.67  tff(c_334, plain, (![A_231]: (v5_pre_topc(k10_tmap_1(A_231, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_tsep_1(A_231, '#skF_3', '#skF_4'), '#skF_2') | ~r4_tsep_1(A_231, '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', A_231) | ~m1_pre_topc('#skF_3', A_231) | ~l1_pre_topc(A_231) | ~v2_pre_topc(A_231) | v2_struct_0(A_231))), inference(negUnitSimplification, [status(thm)], [c_48, c_331])).
% 3.52/1.67  tff(c_195, plain, (![B_191, A_193, F_188, E_189, D_190, C_192]: (v1_funct_2(k10_tmap_1(A_193, B_191, C_192, D_190, E_189, F_188), u1_struct_0(k1_tsep_1(A_193, C_192, D_190)), u1_struct_0(B_191)) | ~m1_subset_1(F_188, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_190), u1_struct_0(B_191)))) | ~v1_funct_2(F_188, u1_struct_0(D_190), u1_struct_0(B_191)) | ~v1_funct_1(F_188) | ~m1_subset_1(E_189, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_192), u1_struct_0(B_191)))) | ~v1_funct_2(E_189, u1_struct_0(C_192), u1_struct_0(B_191)) | ~v1_funct_1(E_189) | ~m1_pre_topc(D_190, A_193) | v2_struct_0(D_190) | ~m1_pre_topc(C_192, A_193) | v2_struct_0(C_192) | ~l1_pre_topc(B_191) | ~v2_pre_topc(B_191) | v2_struct_0(B_191) | ~l1_pre_topc(A_193) | ~v2_pre_topc(A_193) | v2_struct_0(A_193))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.52/1.67  tff(c_147, plain, (![A_181, E_177, C_180, B_179, D_178, F_176]: (m1_subset_1(k10_tmap_1(A_181, B_179, C_180, D_178, E_177, F_176), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_181, C_180, D_178)), u1_struct_0(B_179)))) | ~m1_subset_1(F_176, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_178), u1_struct_0(B_179)))) | ~v1_funct_2(F_176, u1_struct_0(D_178), u1_struct_0(B_179)) | ~v1_funct_1(F_176) | ~m1_subset_1(E_177, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_180), u1_struct_0(B_179)))) | ~v1_funct_2(E_177, u1_struct_0(C_180), u1_struct_0(B_179)) | ~v1_funct_1(E_177) | ~m1_pre_topc(D_178, A_181) | v2_struct_0(D_178) | ~m1_pre_topc(C_180, A_181) | v2_struct_0(C_180) | ~l1_pre_topc(B_179) | ~v2_pre_topc(B_179) | v2_struct_0(B_179) | ~l1_pre_topc(A_181) | ~v2_pre_topc(A_181) | v2_struct_0(A_181))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.52/1.67  tff(c_63, plain, (![B_140, E_138, C_141, A_142, F_137, D_139]: (v1_funct_1(k10_tmap_1(A_142, B_140, C_141, D_139, E_138, F_137)) | ~m1_subset_1(F_137, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_139), u1_struct_0(B_140)))) | ~v1_funct_2(F_137, u1_struct_0(D_139), u1_struct_0(B_140)) | ~v1_funct_1(F_137) | ~m1_subset_1(E_138, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_141), u1_struct_0(B_140)))) | ~v1_funct_2(E_138, u1_struct_0(C_141), u1_struct_0(B_140)) | ~v1_funct_1(E_138) | ~m1_pre_topc(D_139, A_142) | v2_struct_0(D_139) | ~m1_pre_topc(C_141, A_142) | v2_struct_0(C_141) | ~l1_pre_topc(B_140) | ~v2_pre_topc(B_140) | v2_struct_0(B_140) | ~l1_pre_topc(A_142) | ~v2_pre_topc(A_142) | v2_struct_0(A_142))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.52/1.67  tff(c_65, plain, (![A_142, C_141, E_138]: (v1_funct_1(k10_tmap_1(A_142, '#skF_2', C_141, '#skF_4', E_138, '#skF_6')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_138, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_141), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_138, u1_struct_0(C_141), u1_struct_0('#skF_2')) | ~v1_funct_1(E_138) | ~m1_pre_topc('#skF_4', A_142) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_141, A_142) | v2_struct_0(C_141) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_142) | ~v2_pre_topc(A_142) | v2_struct_0(A_142))), inference(resolution, [status(thm)], [c_20, c_63])).
% 3.52/1.67  tff(c_70, plain, (![A_142, C_141, E_138]: (v1_funct_1(k10_tmap_1(A_142, '#skF_2', C_141, '#skF_4', E_138, '#skF_6')) | ~m1_subset_1(E_138, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_141), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_138, u1_struct_0(C_141), u1_struct_0('#skF_2')) | ~v1_funct_1(E_138) | ~m1_pre_topc('#skF_4', A_142) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_141, A_142) | v2_struct_0(C_141) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_142) | ~v2_pre_topc(A_142) | v2_struct_0(A_142))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_26, c_24, c_65])).
% 3.52/1.67  tff(c_77, plain, (![A_149, C_150, E_151]: (v1_funct_1(k10_tmap_1(A_149, '#skF_2', C_150, '#skF_4', E_151, '#skF_6')) | ~m1_subset_1(E_151, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_150), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_151, u1_struct_0(C_150), u1_struct_0('#skF_2')) | ~v1_funct_1(E_151) | ~m1_pre_topc('#skF_4', A_149) | ~m1_pre_topc(C_150, A_149) | v2_struct_0(C_150) | ~l1_pre_topc(A_149) | ~v2_pre_topc(A_149) | v2_struct_0(A_149))), inference(negUnitSimplification, [status(thm)], [c_54, c_42, c_70])).
% 3.52/1.67  tff(c_81, plain, (![A_149]: (v1_funct_1(k10_tmap_1(A_149, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', A_149) | ~m1_pre_topc('#skF_3', A_149) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_149) | ~v2_pre_topc(A_149) | v2_struct_0(A_149))), inference(resolution, [status(thm)], [c_28, c_77])).
% 3.52/1.67  tff(c_88, plain, (![A_149]: (v1_funct_1(k10_tmap_1(A_149, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_4', A_149) | ~m1_pre_topc('#skF_3', A_149) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_149) | ~v2_pre_topc(A_149) | v2_struct_0(A_149))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_81])).
% 3.52/1.67  tff(c_91, plain, (![A_153]: (v1_funct_1(k10_tmap_1(A_153, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_4', A_153) | ~m1_pre_topc('#skF_3', A_153) | ~l1_pre_topc(A_153) | ~v2_pre_topc(A_153) | v2_struct_0(A_153))), inference(negUnitSimplification, [status(thm)], [c_48, c_88])).
% 3.52/1.67  tff(c_18, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_203])).
% 3.52/1.67  tff(c_62, plain, (~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_18])).
% 3.52/1.67  tff(c_94, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_91, c_62])).
% 3.52/1.67  tff(c_97, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_44, c_38, c_94])).
% 3.52/1.67  tff(c_99, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_97])).
% 3.52/1.67  tff(c_100, plain, (~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')) | ~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_18])).
% 3.52/1.67  tff(c_102, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_100])).
% 3.52/1.67  tff(c_158, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_147, c_102])).
% 3.52/1.67  tff(c_170, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_50, c_44, c_38, c_34, c_32, c_28, c_26, c_24, c_20, c_158])).
% 3.52/1.67  tff(c_172, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_48, c_42, c_170])).
% 3.52/1.67  tff(c_173, plain, (~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_100])).
% 3.52/1.67  tff(c_175, plain, (~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_173])).
% 3.52/1.67  tff(c_198, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_195, c_175])).
% 3.52/1.67  tff(c_201, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_50, c_44, c_38, c_34, c_32, c_28, c_26, c_24, c_20, c_198])).
% 3.52/1.67  tff(c_203, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_48, c_42, c_201])).
% 3.52/1.67  tff(c_204, plain, (~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2')), inference(splitRight, [status(thm)], [c_173])).
% 3.52/1.67  tff(c_337, plain, (~r4_tsep_1('#skF_1', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_334, c_204])).
% 3.52/1.67  tff(c_340, plain, (~r4_tsep_1('#skF_1', '#skF_3', '#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_44, c_38, c_337])).
% 3.52/1.67  tff(c_341, plain, (~r4_tsep_1('#skF_1', '#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_60, c_340])).
% 3.52/1.67  tff(c_369, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~v1_borsuk_1('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~v1_borsuk_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_16, c_341])).
% 3.52/1.67  tff(c_372, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_46, c_44, c_40, c_38, c_369])).
% 3.52/1.67  tff(c_374, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_372])).
% 3.52/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.52/1.67  
% 3.52/1.67  Inference rules
% 3.52/1.67  ----------------------
% 3.52/1.67  #Ref     : 0
% 3.52/1.67  #Sup     : 45
% 3.52/1.67  #Fact    : 0
% 3.52/1.67  #Define  : 0
% 3.52/1.67  #Split   : 5
% 3.52/1.67  #Chain   : 0
% 3.52/1.67  #Close   : 0
% 3.52/1.67  
% 3.52/1.67  Ordering : KBO
% 3.52/1.67  
% 3.52/1.67  Simplification rules
% 3.52/1.67  ----------------------
% 3.52/1.67  #Subsume      : 7
% 3.52/1.67  #Demod        : 149
% 3.52/1.67  #Tautology    : 2
% 3.52/1.67  #SimpNegUnit  : 38
% 3.52/1.67  #BackRed      : 0
% 3.52/1.67  
% 3.52/1.67  #Partial instantiations: 0
% 3.52/1.67  #Strategies tried      : 1
% 3.52/1.67  
% 3.52/1.67  Timing (in seconds)
% 3.52/1.67  ----------------------
% 3.52/1.68  Preprocessing        : 0.37
% 3.52/1.68  Parsing              : 0.20
% 3.52/1.68  CNF conversion       : 0.05
% 3.52/1.68  Main loop            : 0.44
% 3.52/1.68  Inferencing          : 0.17
% 3.52/1.68  Reduction            : 0.12
% 3.52/1.68  Demodulation         : 0.09
% 3.52/1.68  BG Simplification    : 0.02
% 3.52/1.68  Subsumption          : 0.09
% 3.52/1.68  Abstraction          : 0.02
% 3.52/1.68  MUC search           : 0.00
% 3.52/1.68  Cooper               : 0.00
% 3.52/1.68  Total                : 0.86
% 3.52/1.68  Index Insertion      : 0.00
% 3.52/1.68  Index Deletion       : 0.00
% 3.52/1.68  Index Matching       : 0.00
% 3.52/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
