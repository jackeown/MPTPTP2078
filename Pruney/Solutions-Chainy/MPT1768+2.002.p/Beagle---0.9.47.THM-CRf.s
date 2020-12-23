%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:16 EST 2020

% Result     : Theorem 3.90s
% Output     : CNFRefutation 3.90s
% Verified   : 
% Statistics : Number of formulae       :  133 (1564 expanded)
%              Number of leaves         :   33 ( 598 expanded)
%              Depth                    :   18
%              Number of atoms          :  534 (12436 expanded)
%              Number of equality atoms :   33 ( 197 expanded)
%              Maximal formula depth    :   28 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_219,negated_conjecture,(
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
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,A) )
                   => ! [E] :
                        ( ( ~ v2_struct_0(E)
                          & m1_pre_topc(E,A) )
                       => ( ( m1_pre_topc(D,C)
                            & m1_pre_topc(E,D) )
                         => ! [F] :
                              ( ( v1_funct_1(F)
                                & v1_funct_2(F,u1_struct_0(C),u1_struct_0(B))
                                & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                             => r2_funct_2(u1_struct_0(E),u1_struct_0(B),k3_tmap_1(A,B,D,E,k3_tmap_1(A,B,C,D,F)),k3_tmap_1(A,B,C,E,F)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_tmap_1)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_34,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_122,axiom,(
    ! [A,B,C,D] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B)
        & v1_funct_1(C)
        & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B))))
        & l1_struct_0(D) )
     => ( v1_funct_1(k2_tmap_1(A,B,C,D))
        & v1_funct_2(k2_tmap_1(A,B,C,D),u1_struct_0(D),u1_struct_0(B))
        & m1_subset_1(k2_tmap_1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tmap_1)).

tff(f_72,axiom,(
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
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => k2_tmap_1(A,B,C,D) = k2_partfun1(u1_struct_0(A),u1_struct_0(B),C,u1_struct_0(D)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_104,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                     => ( m1_pre_topc(D,C)
                       => k3_tmap_1(A,B,C,D,E) = k2_partfun1(u1_struct_0(C),u1_struct_0(B),E,u1_struct_0(D)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

tff(f_172,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,B)
             => m1_pre_topc(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).

tff(f_160,axiom,(
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
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(A),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                     => ( m1_pre_topc(C,D)
                       => r2_funct_2(u1_struct_0(C),u1_struct_0(B),k3_tmap_1(A,B,D,C,k2_tmap_1(A,B,E,D)),k2_tmap_1(A,B,E,C)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_tmap_1)).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_52,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_38,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_58,plain,(
    ! [B_154,A_155] :
      ( l1_pre_topc(B_154)
      | ~ m1_pre_topc(B_154,A_155)
      | ~ l1_pre_topc(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_67,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_58])).

tff(c_80,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_67])).

tff(c_4,plain,(
    ! [A_4] :
      ( l1_struct_0(A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_54,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_89,plain,(
    ! [B_156,A_157] :
      ( v2_pre_topc(B_156)
      | ~ m1_pre_topc(B_156,A_157)
      | ~ l1_pre_topc(A_157)
      | ~ v2_pre_topc(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_98,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_89])).

tff(c_113,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_98])).

tff(c_30,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_34,plain,(
    m1_pre_topc('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_46,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_42,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_70,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_58])).

tff(c_83,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_70])).

tff(c_28,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_26,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_24,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_175,plain,(
    ! [A_164,B_165,C_166,D_167] :
      ( v1_funct_1(k2_tmap_1(A_164,B_165,C_166,D_167))
      | ~ l1_struct_0(D_167)
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_164),u1_struct_0(B_165))))
      | ~ v1_funct_2(C_166,u1_struct_0(A_164),u1_struct_0(B_165))
      | ~ v1_funct_1(C_166)
      | ~ l1_struct_0(B_165)
      | ~ l1_struct_0(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_177,plain,(
    ! [D_167] :
      ( v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6',D_167))
      | ~ l1_struct_0(D_167)
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_175])).

tff(c_180,plain,(
    ! [D_167] :
      ( v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6',D_167))
      | ~ l1_struct_0(D_167)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_177])).

tff(c_200,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_180])).

tff(c_244,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_200])).

tff(c_248,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_244])).

tff(c_249,plain,(
    ! [D_167] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6',D_167))
      | ~ l1_struct_0(D_167) ) ),
    inference(splitRight,[status(thm)],[c_180])).

tff(c_251,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_249])).

tff(c_254,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_251])).

tff(c_258,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_254])).

tff(c_259,plain,(
    ! [D_167] :
      ( v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6',D_167))
      | ~ l1_struct_0(D_167) ) ),
    inference(splitRight,[status(thm)],[c_249])).

tff(c_250,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_180])).

tff(c_260,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_249])).

tff(c_261,plain,(
    ! [A_172,B_173,C_174,D_175] :
      ( v1_funct_2(k2_tmap_1(A_172,B_173,C_174,D_175),u1_struct_0(D_175),u1_struct_0(B_173))
      | ~ l1_struct_0(D_175)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_172),u1_struct_0(B_173))))
      | ~ v1_funct_2(C_174,u1_struct_0(A_172),u1_struct_0(B_173))
      | ~ v1_funct_1(C_174)
      | ~ l1_struct_0(B_173)
      | ~ l1_struct_0(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_263,plain,(
    ! [D_175] :
      ( v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_6',D_175),u1_struct_0(D_175),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_175)
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_261])).

tff(c_266,plain,(
    ! [D_175] :
      ( v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_6',D_175),u1_struct_0(D_175),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_175) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_260,c_28,c_26,c_263])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_48,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_12,plain,(
    ! [A_54,B_55,C_56,D_57] :
      ( m1_subset_1(k2_tmap_1(A_54,B_55,C_56,D_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_57),u1_struct_0(B_55))))
      | ~ l1_struct_0(D_57)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_54),u1_struct_0(B_55))))
      | ~ v1_funct_2(C_56,u1_struct_0(A_54),u1_struct_0(B_55))
      | ~ v1_funct_1(C_56)
      | ~ l1_struct_0(B_55)
      | ~ l1_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_402,plain,(
    ! [A_188,B_189,C_190,D_191] :
      ( k2_partfun1(u1_struct_0(A_188),u1_struct_0(B_189),C_190,u1_struct_0(D_191)) = k2_tmap_1(A_188,B_189,C_190,D_191)
      | ~ m1_pre_topc(D_191,A_188)
      | ~ m1_subset_1(C_190,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_188),u1_struct_0(B_189))))
      | ~ v1_funct_2(C_190,u1_struct_0(A_188),u1_struct_0(B_189))
      | ~ v1_funct_1(C_190)
      | ~ l1_pre_topc(B_189)
      | ~ v2_pre_topc(B_189)
      | v2_struct_0(B_189)
      | ~ l1_pre_topc(A_188)
      | ~ v2_pre_topc(A_188)
      | v2_struct_0(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_699,plain,(
    ! [D_220,C_221,D_224,A_222,B_223] :
      ( k2_partfun1(u1_struct_0(D_224),u1_struct_0(B_223),k2_tmap_1(A_222,B_223,C_221,D_224),u1_struct_0(D_220)) = k2_tmap_1(D_224,B_223,k2_tmap_1(A_222,B_223,C_221,D_224),D_220)
      | ~ m1_pre_topc(D_220,D_224)
      | ~ v1_funct_2(k2_tmap_1(A_222,B_223,C_221,D_224),u1_struct_0(D_224),u1_struct_0(B_223))
      | ~ v1_funct_1(k2_tmap_1(A_222,B_223,C_221,D_224))
      | ~ l1_pre_topc(B_223)
      | ~ v2_pre_topc(B_223)
      | v2_struct_0(B_223)
      | ~ l1_pre_topc(D_224)
      | ~ v2_pre_topc(D_224)
      | v2_struct_0(D_224)
      | ~ l1_struct_0(D_224)
      | ~ m1_subset_1(C_221,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_222),u1_struct_0(B_223))))
      | ~ v1_funct_2(C_221,u1_struct_0(A_222),u1_struct_0(B_223))
      | ~ v1_funct_1(C_221)
      | ~ l1_struct_0(B_223)
      | ~ l1_struct_0(A_222) ) ),
    inference(resolution,[status(thm)],[c_12,c_402])).

tff(c_703,plain,(
    ! [D_224,D_220] :
      ( k2_partfun1(u1_struct_0(D_224),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_6',D_224),u1_struct_0(D_220)) = k2_tmap_1(D_224,'#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_6',D_224),D_220)
      | ~ m1_pre_topc(D_220,D_224)
      | ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_6',D_224),u1_struct_0(D_224),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6',D_224))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(D_224)
      | ~ v2_pre_topc(D_224)
      | v2_struct_0(D_224)
      | ~ l1_struct_0(D_224)
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_699])).

tff(c_707,plain,(
    ! [D_224,D_220] :
      ( k2_partfun1(u1_struct_0(D_224),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_6',D_224),u1_struct_0(D_220)) = k2_tmap_1(D_224,'#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_6',D_224),D_220)
      | ~ m1_pre_topc(D_220,D_224)
      | ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_6',D_224),u1_struct_0(D_224),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6',D_224))
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(D_224)
      | ~ v2_pre_topc(D_224)
      | v2_struct_0(D_224)
      | ~ l1_struct_0(D_224) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_260,c_28,c_26,c_48,c_46,c_703])).

tff(c_708,plain,(
    ! [D_224,D_220] :
      ( k2_partfun1(u1_struct_0(D_224),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_6',D_224),u1_struct_0(D_220)) = k2_tmap_1(D_224,'#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_6',D_224),D_220)
      | ~ m1_pre_topc(D_220,D_224)
      | ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_6',D_224),u1_struct_0(D_224),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6',D_224))
      | ~ l1_pre_topc(D_224)
      | ~ v2_pre_topc(D_224)
      | v2_struct_0(D_224)
      | ~ l1_struct_0(D_224) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_707])).

tff(c_428,plain,(
    ! [C_203,D_201,E_200,B_202,A_204] :
      ( k3_tmap_1(A_204,B_202,C_203,D_201,E_200) = k2_partfun1(u1_struct_0(C_203),u1_struct_0(B_202),E_200,u1_struct_0(D_201))
      | ~ m1_pre_topc(D_201,C_203)
      | ~ m1_subset_1(E_200,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_203),u1_struct_0(B_202))))
      | ~ v1_funct_2(E_200,u1_struct_0(C_203),u1_struct_0(B_202))
      | ~ v1_funct_1(E_200)
      | ~ m1_pre_topc(D_201,A_204)
      | ~ m1_pre_topc(C_203,A_204)
      | ~ l1_pre_topc(B_202)
      | ~ v2_pre_topc(B_202)
      | v2_struct_0(B_202)
      | ~ l1_pre_topc(A_204)
      | ~ v2_pre_topc(A_204)
      | v2_struct_0(A_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_746,plain,(
    ! [A_230,D_234,C_231,B_233,A_232,D_229] :
      ( k3_tmap_1(A_230,B_233,D_234,D_229,k2_tmap_1(A_232,B_233,C_231,D_234)) = k2_partfun1(u1_struct_0(D_234),u1_struct_0(B_233),k2_tmap_1(A_232,B_233,C_231,D_234),u1_struct_0(D_229))
      | ~ m1_pre_topc(D_229,D_234)
      | ~ v1_funct_2(k2_tmap_1(A_232,B_233,C_231,D_234),u1_struct_0(D_234),u1_struct_0(B_233))
      | ~ v1_funct_1(k2_tmap_1(A_232,B_233,C_231,D_234))
      | ~ m1_pre_topc(D_229,A_230)
      | ~ m1_pre_topc(D_234,A_230)
      | ~ l1_pre_topc(B_233)
      | ~ v2_pre_topc(B_233)
      | v2_struct_0(B_233)
      | ~ l1_pre_topc(A_230)
      | ~ v2_pre_topc(A_230)
      | v2_struct_0(A_230)
      | ~ l1_struct_0(D_234)
      | ~ m1_subset_1(C_231,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_232),u1_struct_0(B_233))))
      | ~ v1_funct_2(C_231,u1_struct_0(A_232),u1_struct_0(B_233))
      | ~ v1_funct_1(C_231)
      | ~ l1_struct_0(B_233)
      | ~ l1_struct_0(A_232) ) ),
    inference(resolution,[status(thm)],[c_12,c_428])).

tff(c_750,plain,(
    ! [A_230,D_234,D_229] :
      ( k3_tmap_1(A_230,'#skF_2',D_234,D_229,k2_tmap_1('#skF_3','#skF_2','#skF_6',D_234)) = k2_partfun1(u1_struct_0(D_234),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_6',D_234),u1_struct_0(D_229))
      | ~ m1_pre_topc(D_229,D_234)
      | ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_6',D_234),u1_struct_0(D_234),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6',D_234))
      | ~ m1_pre_topc(D_229,A_230)
      | ~ m1_pre_topc(D_234,A_230)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_230)
      | ~ v2_pre_topc(A_230)
      | v2_struct_0(A_230)
      | ~ l1_struct_0(D_234)
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_746])).

tff(c_754,plain,(
    ! [A_230,D_234,D_229] :
      ( k3_tmap_1(A_230,'#skF_2',D_234,D_229,k2_tmap_1('#skF_3','#skF_2','#skF_6',D_234)) = k2_partfun1(u1_struct_0(D_234),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_6',D_234),u1_struct_0(D_229))
      | ~ m1_pre_topc(D_229,D_234)
      | ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_6',D_234),u1_struct_0(D_234),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6',D_234))
      | ~ m1_pre_topc(D_229,A_230)
      | ~ m1_pre_topc(D_234,A_230)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_230)
      | ~ v2_pre_topc(A_230)
      | v2_struct_0(A_230)
      | ~ l1_struct_0(D_234) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_260,c_28,c_26,c_48,c_46,c_750])).

tff(c_756,plain,(
    ! [A_235,D_236,D_237] :
      ( k3_tmap_1(A_235,'#skF_2',D_236,D_237,k2_tmap_1('#skF_3','#skF_2','#skF_6',D_236)) = k2_partfun1(u1_struct_0(D_236),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_6',D_236),u1_struct_0(D_237))
      | ~ m1_pre_topc(D_237,D_236)
      | ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_6',D_236),u1_struct_0(D_236),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6',D_236))
      | ~ m1_pre_topc(D_237,A_235)
      | ~ m1_pre_topc(D_236,A_235)
      | ~ l1_pre_topc(A_235)
      | ~ v2_pre_topc(A_235)
      | v2_struct_0(A_235)
      | ~ l1_struct_0(D_236) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_754])).

tff(c_790,plain,(
    ! [A_250,D_251,D_252] :
      ( k3_tmap_1(A_250,'#skF_2',D_251,D_252,k2_tmap_1('#skF_3','#skF_2','#skF_6',D_251)) = k2_tmap_1(D_251,'#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_6',D_251),D_252)
      | ~ m1_pre_topc(D_252,D_251)
      | ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_6',D_251),u1_struct_0(D_251),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6',D_251))
      | ~ m1_pre_topc(D_252,A_250)
      | ~ m1_pre_topc(D_251,A_250)
      | ~ l1_pre_topc(A_250)
      | ~ v2_pre_topc(A_250)
      | v2_struct_0(A_250)
      | ~ l1_struct_0(D_251)
      | ~ m1_pre_topc(D_252,D_251)
      | ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_6',D_251),u1_struct_0(D_251),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6',D_251))
      | ~ l1_pre_topc(D_251)
      | ~ v2_pre_topc(D_251)
      | v2_struct_0(D_251)
      | ~ l1_struct_0(D_251) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_708,c_756])).

tff(c_795,plain,(
    ! [A_256,D_257,D_258] :
      ( k3_tmap_1(A_256,'#skF_2',D_257,D_258,k2_tmap_1('#skF_3','#skF_2','#skF_6',D_257)) = k2_tmap_1(D_257,'#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_6',D_257),D_258)
      | ~ m1_pre_topc(D_258,A_256)
      | ~ m1_pre_topc(D_257,A_256)
      | ~ l1_pre_topc(A_256)
      | ~ v2_pre_topc(A_256)
      | v2_struct_0(A_256)
      | ~ m1_pre_topc(D_258,D_257)
      | ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_6',D_257),u1_struct_0(D_257),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6',D_257))
      | ~ l1_pre_topc(D_257)
      | ~ v2_pre_topc(D_257)
      | v2_struct_0(D_257)
      | ~ l1_struct_0(D_257) ) ),
    inference(resolution,[status(thm)],[c_266,c_790])).

tff(c_799,plain,(
    ! [A_259,D_260,D_261] :
      ( k3_tmap_1(A_259,'#skF_2',D_260,D_261,k2_tmap_1('#skF_3','#skF_2','#skF_6',D_260)) = k2_tmap_1(D_260,'#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_6',D_260),D_261)
      | ~ m1_pre_topc(D_261,A_259)
      | ~ m1_pre_topc(D_260,A_259)
      | ~ l1_pre_topc(A_259)
      | ~ v2_pre_topc(A_259)
      | v2_struct_0(A_259)
      | ~ m1_pre_topc(D_261,D_260)
      | ~ v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6',D_260))
      | ~ l1_pre_topc(D_260)
      | ~ v2_pre_topc(D_260)
      | v2_struct_0(D_260)
      | ~ l1_struct_0(D_260) ) ),
    inference(resolution,[status(thm)],[c_266,c_795])).

tff(c_803,plain,(
    ! [A_262,D_263,D_264] :
      ( k3_tmap_1(A_262,'#skF_2',D_263,D_264,k2_tmap_1('#skF_3','#skF_2','#skF_6',D_263)) = k2_tmap_1(D_263,'#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_6',D_263),D_264)
      | ~ m1_pre_topc(D_264,A_262)
      | ~ m1_pre_topc(D_263,A_262)
      | ~ l1_pre_topc(A_262)
      | ~ v2_pre_topc(A_262)
      | v2_struct_0(A_262)
      | ~ m1_pre_topc(D_264,D_263)
      | ~ l1_pre_topc(D_263)
      | ~ v2_pre_topc(D_263)
      | v2_struct_0(D_263)
      | ~ l1_struct_0(D_263) ) ),
    inference(resolution,[status(thm)],[c_259,c_799])).

tff(c_101,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_89])).

tff(c_116,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_101])).

tff(c_32,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_120,plain,(
    ! [C_158,A_159,B_160] :
      ( m1_pre_topc(C_158,A_159)
      | ~ m1_pre_topc(C_158,B_160)
      | ~ m1_pre_topc(B_160,A_159)
      | ~ l1_pre_topc(A_159)
      | ~ v2_pre_topc(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_131,plain,(
    ! [A_159] :
      ( m1_pre_topc('#skF_5',A_159)
      | ~ m1_pre_topc('#skF_4',A_159)
      | ~ l1_pre_topc(A_159)
      | ~ v2_pre_topc(A_159) ) ),
    inference(resolution,[status(thm)],[c_30,c_120])).

tff(c_432,plain,(
    ! [A_204,D_201] :
      ( k3_tmap_1(A_204,'#skF_2','#skF_3',D_201,'#skF_6') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_201))
      | ~ m1_pre_topc(D_201,'#skF_3')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_201,A_204)
      | ~ m1_pre_topc('#skF_3',A_204)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_204)
      | ~ v2_pre_topc(A_204)
      | v2_struct_0(A_204) ) ),
    inference(resolution,[status(thm)],[c_24,c_428])).

tff(c_436,plain,(
    ! [A_204,D_201] :
      ( k3_tmap_1(A_204,'#skF_2','#skF_3',D_201,'#skF_6') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_201))
      | ~ m1_pre_topc(D_201,'#skF_3')
      | ~ m1_pre_topc(D_201,A_204)
      | ~ m1_pre_topc('#skF_3',A_204)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_204)
      | ~ v2_pre_topc(A_204)
      | v2_struct_0(A_204) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_28,c_26,c_432])).

tff(c_438,plain,(
    ! [A_205,D_206] :
      ( k3_tmap_1(A_205,'#skF_2','#skF_3',D_206,'#skF_6') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_206))
      | ~ m1_pre_topc(D_206,'#skF_3')
      | ~ m1_pre_topc(D_206,A_205)
      | ~ m1_pre_topc('#skF_3',A_205)
      | ~ l1_pre_topc(A_205)
      | ~ v2_pre_topc(A_205)
      | v2_struct_0(A_205) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_436])).

tff(c_448,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5','#skF_6')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_438])).

tff(c_464,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5','#skF_6')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_42,c_448])).

tff(c_465,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5','#skF_6')
    | ~ m1_pre_topc('#skF_5','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_464])).

tff(c_500,plain,(
    ~ m1_pre_topc('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_465])).

tff(c_503,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_131,c_500])).

tff(c_510,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_83,c_32,c_503])).

tff(c_512,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_465])).

tff(c_511,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_465])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_406,plain,(
    ! [D_191] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_191)) = k2_tmap_1('#skF_3','#skF_2','#skF_6',D_191)
      | ~ m1_pre_topc(D_191,'#skF_3')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_402])).

tff(c_410,plain,(
    ! [D_191] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_191)) = k2_tmap_1('#skF_3','#skF_2','#skF_6',D_191)
      | ~ m1_pre_topc(D_191,'#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_83,c_48,c_46,c_28,c_26,c_406])).

tff(c_411,plain,(
    ! [D_191] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_191)) = k2_tmap_1('#skF_3','#skF_2','#skF_6',D_191)
      | ~ m1_pre_topc(D_191,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_50,c_410])).

tff(c_602,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5','#skF_6') = k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_511,c_411])).

tff(c_609,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5','#skF_6') = k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_512,c_602])).

tff(c_450,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_438])).

tff(c_468,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_42,c_32,c_450])).

tff(c_469,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_468])).

tff(c_482,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6') = k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_469,c_411])).

tff(c_489,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6') = k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_482])).

tff(c_22,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5',k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6')),k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_494,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4')),k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_489,c_22])).

tff(c_718,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4')),k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_609,c_494])).

tff(c_812,plain,
    ( ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),'#skF_5'),k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_5'))
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_803,c_718])).

tff(c_825,plain,
    ( ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),'#skF_5'),k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_5'))
    | v2_struct_0('#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_80,c_30,c_54,c_52,c_38,c_34,c_812])).

tff(c_826,plain,
    ( ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),'#skF_5'),k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_5'))
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_56,c_825])).

tff(c_831,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_826])).

tff(c_843,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_831])).

tff(c_847,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_843])).

tff(c_849,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_826])).

tff(c_18,plain,(
    ! [A_58,E_88,B_74,D_86,C_82] :
      ( r2_funct_2(u1_struct_0(C_82),u1_struct_0(B_74),k3_tmap_1(A_58,B_74,D_86,C_82,k2_tmap_1(A_58,B_74,E_88,D_86)),k2_tmap_1(A_58,B_74,E_88,C_82))
      | ~ m1_pre_topc(C_82,D_86)
      | ~ m1_subset_1(E_88,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_58),u1_struct_0(B_74))))
      | ~ v1_funct_2(E_88,u1_struct_0(A_58),u1_struct_0(B_74))
      | ~ v1_funct_1(E_88)
      | ~ m1_pre_topc(D_86,A_58)
      | v2_struct_0(D_86)
      | ~ m1_pre_topc(C_82,A_58)
      | v2_struct_0(C_82)
      | ~ l1_pre_topc(B_74)
      | ~ v2_pre_topc(B_74)
      | v2_struct_0(B_74)
      | ~ l1_pre_topc(A_58)
      | ~ v2_pre_topc(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_816,plain,(
    ! [D_264,D_263] :
      ( r2_funct_2(u1_struct_0(D_264),u1_struct_0('#skF_2'),k2_tmap_1(D_263,'#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_6',D_263),D_264),k2_tmap_1('#skF_3','#skF_2','#skF_6',D_264))
      | ~ m1_pre_topc(D_264,D_263)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_263,'#skF_3')
      | v2_struct_0(D_263)
      | ~ m1_pre_topc(D_264,'#skF_3')
      | v2_struct_0(D_264)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(D_264,'#skF_3')
      | ~ m1_pre_topc(D_263,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(D_264,D_263)
      | ~ l1_pre_topc(D_263)
      | ~ v2_pre_topc(D_263)
      | v2_struct_0(D_263)
      | ~ l1_struct_0(D_263) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_803,c_18])).

tff(c_828,plain,(
    ! [D_264,D_263] :
      ( r2_funct_2(u1_struct_0(D_264),u1_struct_0('#skF_2'),k2_tmap_1(D_263,'#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_6',D_263),D_264),k2_tmap_1('#skF_3','#skF_2','#skF_6',D_264))
      | v2_struct_0(D_264)
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(D_264,'#skF_3')
      | ~ m1_pre_topc(D_263,'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(D_264,D_263)
      | ~ l1_pre_topc(D_263)
      | ~ v2_pre_topc(D_263)
      | v2_struct_0(D_263)
      | ~ l1_struct_0(D_263) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_83,c_116,c_83,c_48,c_46,c_28,c_26,c_24,c_816])).

tff(c_850,plain,(
    ! [D_271,D_272] :
      ( r2_funct_2(u1_struct_0(D_271),u1_struct_0('#skF_2'),k2_tmap_1(D_272,'#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_6',D_272),D_271),k2_tmap_1('#skF_3','#skF_2','#skF_6',D_271))
      | v2_struct_0(D_271)
      | ~ m1_pre_topc(D_271,'#skF_3')
      | ~ m1_pre_topc(D_272,'#skF_3')
      | ~ m1_pre_topc(D_271,D_272)
      | ~ l1_pre_topc(D_272)
      | ~ v2_pre_topc(D_272)
      | v2_struct_0(D_272)
      | ~ l1_struct_0(D_272) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_50,c_828])).

tff(c_848,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_4'),'#skF_5'),k2_tmap_1('#skF_3','#skF_2','#skF_6','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_826])).

tff(c_853,plain,
    ( v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_850,c_848])).

tff(c_856,plain,
    ( v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_849,c_113,c_80,c_30,c_32,c_512,c_853])).

tff(c_858,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_36,c_856])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:54:55 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.90/1.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.90/1.70  
% 3.90/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.90/1.70  %$ r2_funct_2 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.90/1.70  
% 3.90/1.70  %Foreground sorts:
% 3.90/1.70  
% 3.90/1.70  
% 3.90/1.70  %Background operators:
% 3.90/1.70  
% 3.90/1.70  
% 3.90/1.70  %Foreground operators:
% 3.90/1.70  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.90/1.70  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.90/1.70  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.90/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.90/1.70  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.90/1.70  tff('#skF_5', type, '#skF_5': $i).
% 3.90/1.70  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.90/1.70  tff('#skF_6', type, '#skF_6': $i).
% 3.90/1.70  tff('#skF_2', type, '#skF_2': $i).
% 3.90/1.70  tff('#skF_3', type, '#skF_3': $i).
% 3.90/1.70  tff('#skF_1', type, '#skF_1': $i).
% 3.90/1.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.90/1.70  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.90/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.90/1.70  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.90/1.70  tff('#skF_4', type, '#skF_4': $i).
% 3.90/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.90/1.70  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.90/1.70  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.90/1.70  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.90/1.70  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.90/1.70  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.90/1.70  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 3.90/1.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.90/1.70  
% 3.90/1.72  tff(f_219, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: ((~v2_struct_0(E) & m1_pre_topc(E, A)) => ((m1_pre_topc(D, C) & m1_pre_topc(E, D)) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => r2_funct_2(u1_struct_0(E), u1_struct_0(B), k3_tmap_1(A, B, D, E, k3_tmap_1(A, B, C, D, F)), k3_tmap_1(A, B, C, E, F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_tmap_1)).
% 3.90/1.72  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.90/1.72  tff(f_38, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.90/1.72  tff(f_34, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.90/1.72  tff(f_122, axiom, (![A, B, C, D]: ((((((l1_struct_0(A) & l1_struct_0(B)) & v1_funct_1(C)) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) & l1_struct_0(D)) => ((v1_funct_1(k2_tmap_1(A, B, C, D)) & v1_funct_2(k2_tmap_1(A, B, C, D), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k2_tmap_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tmap_1)).
% 3.90/1.72  tff(f_72, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 3.90/1.72  tff(f_104, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 3.90/1.72  tff(f_172, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, B) => m1_pre_topc(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tsep_1)).
% 3.90/1.72  tff(f_160, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (m1_pre_topc(C, D) => r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, D, C, k2_tmap_1(A, B, E, D)), k2_tmap_1(A, B, E, C))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_tmap_1)).
% 3.90/1.72  tff(c_40, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.90/1.72  tff(c_36, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.90/1.72  tff(c_52, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.90/1.72  tff(c_38, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.90/1.72  tff(c_58, plain, (![B_154, A_155]: (l1_pre_topc(B_154) | ~m1_pre_topc(B_154, A_155) | ~l1_pre_topc(A_155))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.90/1.72  tff(c_67, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_58])).
% 3.90/1.72  tff(c_80, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_67])).
% 3.90/1.72  tff(c_4, plain, (![A_4]: (l1_struct_0(A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.90/1.72  tff(c_56, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.90/1.72  tff(c_54, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.90/1.72  tff(c_89, plain, (![B_156, A_157]: (v2_pre_topc(B_156) | ~m1_pre_topc(B_156, A_157) | ~l1_pre_topc(A_157) | ~v2_pre_topc(A_157))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.90/1.72  tff(c_98, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_89])).
% 3.90/1.72  tff(c_113, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_98])).
% 3.90/1.72  tff(c_30, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.90/1.72  tff(c_34, plain, (m1_pre_topc('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.90/1.72  tff(c_46, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.90/1.72  tff(c_42, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.90/1.72  tff(c_70, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_58])).
% 3.90/1.72  tff(c_83, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_70])).
% 3.90/1.72  tff(c_28, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.90/1.72  tff(c_26, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.90/1.72  tff(c_24, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.90/1.72  tff(c_175, plain, (![A_164, B_165, C_166, D_167]: (v1_funct_1(k2_tmap_1(A_164, B_165, C_166, D_167)) | ~l1_struct_0(D_167) | ~m1_subset_1(C_166, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_164), u1_struct_0(B_165)))) | ~v1_funct_2(C_166, u1_struct_0(A_164), u1_struct_0(B_165)) | ~v1_funct_1(C_166) | ~l1_struct_0(B_165) | ~l1_struct_0(A_164))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.90/1.72  tff(c_177, plain, (![D_167]: (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_167)) | ~l1_struct_0(D_167) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_24, c_175])).
% 3.90/1.72  tff(c_180, plain, (![D_167]: (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_167)) | ~l1_struct_0(D_167) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_177])).
% 3.90/1.72  tff(c_200, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_180])).
% 3.90/1.72  tff(c_244, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_4, c_200])).
% 3.90/1.72  tff(c_248, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83, c_244])).
% 3.90/1.72  tff(c_249, plain, (![D_167]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_167)) | ~l1_struct_0(D_167))), inference(splitRight, [status(thm)], [c_180])).
% 3.90/1.72  tff(c_251, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_249])).
% 3.90/1.72  tff(c_254, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4, c_251])).
% 3.90/1.72  tff(c_258, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_254])).
% 3.90/1.72  tff(c_259, plain, (![D_167]: (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_167)) | ~l1_struct_0(D_167))), inference(splitRight, [status(thm)], [c_249])).
% 3.90/1.72  tff(c_250, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_180])).
% 3.90/1.72  tff(c_260, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_249])).
% 3.90/1.72  tff(c_261, plain, (![A_172, B_173, C_174, D_175]: (v1_funct_2(k2_tmap_1(A_172, B_173, C_174, D_175), u1_struct_0(D_175), u1_struct_0(B_173)) | ~l1_struct_0(D_175) | ~m1_subset_1(C_174, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_172), u1_struct_0(B_173)))) | ~v1_funct_2(C_174, u1_struct_0(A_172), u1_struct_0(B_173)) | ~v1_funct_1(C_174) | ~l1_struct_0(B_173) | ~l1_struct_0(A_172))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.90/1.72  tff(c_263, plain, (![D_175]: (v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_175), u1_struct_0(D_175), u1_struct_0('#skF_2')) | ~l1_struct_0(D_175) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_24, c_261])).
% 3.90/1.72  tff(c_266, plain, (![D_175]: (v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_175), u1_struct_0(D_175), u1_struct_0('#skF_2')) | ~l1_struct_0(D_175))), inference(demodulation, [status(thm), theory('equality')], [c_250, c_260, c_28, c_26, c_263])).
% 3.90/1.72  tff(c_50, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.90/1.72  tff(c_48, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.90/1.72  tff(c_12, plain, (![A_54, B_55, C_56, D_57]: (m1_subset_1(k2_tmap_1(A_54, B_55, C_56, D_57), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_57), u1_struct_0(B_55)))) | ~l1_struct_0(D_57) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_54), u1_struct_0(B_55)))) | ~v1_funct_2(C_56, u1_struct_0(A_54), u1_struct_0(B_55)) | ~v1_funct_1(C_56) | ~l1_struct_0(B_55) | ~l1_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.90/1.72  tff(c_402, plain, (![A_188, B_189, C_190, D_191]: (k2_partfun1(u1_struct_0(A_188), u1_struct_0(B_189), C_190, u1_struct_0(D_191))=k2_tmap_1(A_188, B_189, C_190, D_191) | ~m1_pre_topc(D_191, A_188) | ~m1_subset_1(C_190, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_188), u1_struct_0(B_189)))) | ~v1_funct_2(C_190, u1_struct_0(A_188), u1_struct_0(B_189)) | ~v1_funct_1(C_190) | ~l1_pre_topc(B_189) | ~v2_pre_topc(B_189) | v2_struct_0(B_189) | ~l1_pre_topc(A_188) | ~v2_pre_topc(A_188) | v2_struct_0(A_188))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.90/1.72  tff(c_699, plain, (![D_220, C_221, D_224, A_222, B_223]: (k2_partfun1(u1_struct_0(D_224), u1_struct_0(B_223), k2_tmap_1(A_222, B_223, C_221, D_224), u1_struct_0(D_220))=k2_tmap_1(D_224, B_223, k2_tmap_1(A_222, B_223, C_221, D_224), D_220) | ~m1_pre_topc(D_220, D_224) | ~v1_funct_2(k2_tmap_1(A_222, B_223, C_221, D_224), u1_struct_0(D_224), u1_struct_0(B_223)) | ~v1_funct_1(k2_tmap_1(A_222, B_223, C_221, D_224)) | ~l1_pre_topc(B_223) | ~v2_pre_topc(B_223) | v2_struct_0(B_223) | ~l1_pre_topc(D_224) | ~v2_pre_topc(D_224) | v2_struct_0(D_224) | ~l1_struct_0(D_224) | ~m1_subset_1(C_221, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_222), u1_struct_0(B_223)))) | ~v1_funct_2(C_221, u1_struct_0(A_222), u1_struct_0(B_223)) | ~v1_funct_1(C_221) | ~l1_struct_0(B_223) | ~l1_struct_0(A_222))), inference(resolution, [status(thm)], [c_12, c_402])).
% 3.90/1.72  tff(c_703, plain, (![D_224, D_220]: (k2_partfun1(u1_struct_0(D_224), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_224), u1_struct_0(D_220))=k2_tmap_1(D_224, '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_224), D_220) | ~m1_pre_topc(D_220, D_224) | ~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_224), u1_struct_0(D_224), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_224)) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(D_224) | ~v2_pre_topc(D_224) | v2_struct_0(D_224) | ~l1_struct_0(D_224) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_24, c_699])).
% 3.90/1.72  tff(c_707, plain, (![D_224, D_220]: (k2_partfun1(u1_struct_0(D_224), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_224), u1_struct_0(D_220))=k2_tmap_1(D_224, '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_224), D_220) | ~m1_pre_topc(D_220, D_224) | ~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_224), u1_struct_0(D_224), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_224)) | v2_struct_0('#skF_2') | ~l1_pre_topc(D_224) | ~v2_pre_topc(D_224) | v2_struct_0(D_224) | ~l1_struct_0(D_224))), inference(demodulation, [status(thm), theory('equality')], [c_250, c_260, c_28, c_26, c_48, c_46, c_703])).
% 3.90/1.72  tff(c_708, plain, (![D_224, D_220]: (k2_partfun1(u1_struct_0(D_224), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_224), u1_struct_0(D_220))=k2_tmap_1(D_224, '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_224), D_220) | ~m1_pre_topc(D_220, D_224) | ~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_224), u1_struct_0(D_224), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_224)) | ~l1_pre_topc(D_224) | ~v2_pre_topc(D_224) | v2_struct_0(D_224) | ~l1_struct_0(D_224))), inference(negUnitSimplification, [status(thm)], [c_50, c_707])).
% 3.90/1.72  tff(c_428, plain, (![C_203, D_201, E_200, B_202, A_204]: (k3_tmap_1(A_204, B_202, C_203, D_201, E_200)=k2_partfun1(u1_struct_0(C_203), u1_struct_0(B_202), E_200, u1_struct_0(D_201)) | ~m1_pre_topc(D_201, C_203) | ~m1_subset_1(E_200, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_203), u1_struct_0(B_202)))) | ~v1_funct_2(E_200, u1_struct_0(C_203), u1_struct_0(B_202)) | ~v1_funct_1(E_200) | ~m1_pre_topc(D_201, A_204) | ~m1_pre_topc(C_203, A_204) | ~l1_pre_topc(B_202) | ~v2_pre_topc(B_202) | v2_struct_0(B_202) | ~l1_pre_topc(A_204) | ~v2_pre_topc(A_204) | v2_struct_0(A_204))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.90/1.72  tff(c_746, plain, (![A_230, D_234, C_231, B_233, A_232, D_229]: (k3_tmap_1(A_230, B_233, D_234, D_229, k2_tmap_1(A_232, B_233, C_231, D_234))=k2_partfun1(u1_struct_0(D_234), u1_struct_0(B_233), k2_tmap_1(A_232, B_233, C_231, D_234), u1_struct_0(D_229)) | ~m1_pre_topc(D_229, D_234) | ~v1_funct_2(k2_tmap_1(A_232, B_233, C_231, D_234), u1_struct_0(D_234), u1_struct_0(B_233)) | ~v1_funct_1(k2_tmap_1(A_232, B_233, C_231, D_234)) | ~m1_pre_topc(D_229, A_230) | ~m1_pre_topc(D_234, A_230) | ~l1_pre_topc(B_233) | ~v2_pre_topc(B_233) | v2_struct_0(B_233) | ~l1_pre_topc(A_230) | ~v2_pre_topc(A_230) | v2_struct_0(A_230) | ~l1_struct_0(D_234) | ~m1_subset_1(C_231, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_232), u1_struct_0(B_233)))) | ~v1_funct_2(C_231, u1_struct_0(A_232), u1_struct_0(B_233)) | ~v1_funct_1(C_231) | ~l1_struct_0(B_233) | ~l1_struct_0(A_232))), inference(resolution, [status(thm)], [c_12, c_428])).
% 3.90/1.72  tff(c_750, plain, (![A_230, D_234, D_229]: (k3_tmap_1(A_230, '#skF_2', D_234, D_229, k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_234))=k2_partfun1(u1_struct_0(D_234), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_234), u1_struct_0(D_229)) | ~m1_pre_topc(D_229, D_234) | ~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_234), u1_struct_0(D_234), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_234)) | ~m1_pre_topc(D_229, A_230) | ~m1_pre_topc(D_234, A_230) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_230) | ~v2_pre_topc(A_230) | v2_struct_0(A_230) | ~l1_struct_0(D_234) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_24, c_746])).
% 3.90/1.72  tff(c_754, plain, (![A_230, D_234, D_229]: (k3_tmap_1(A_230, '#skF_2', D_234, D_229, k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_234))=k2_partfun1(u1_struct_0(D_234), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_234), u1_struct_0(D_229)) | ~m1_pre_topc(D_229, D_234) | ~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_234), u1_struct_0(D_234), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_234)) | ~m1_pre_topc(D_229, A_230) | ~m1_pre_topc(D_234, A_230) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_230) | ~v2_pre_topc(A_230) | v2_struct_0(A_230) | ~l1_struct_0(D_234))), inference(demodulation, [status(thm), theory('equality')], [c_250, c_260, c_28, c_26, c_48, c_46, c_750])).
% 3.90/1.72  tff(c_756, plain, (![A_235, D_236, D_237]: (k3_tmap_1(A_235, '#skF_2', D_236, D_237, k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_236))=k2_partfun1(u1_struct_0(D_236), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_236), u1_struct_0(D_237)) | ~m1_pre_topc(D_237, D_236) | ~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_236), u1_struct_0(D_236), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_236)) | ~m1_pre_topc(D_237, A_235) | ~m1_pre_topc(D_236, A_235) | ~l1_pre_topc(A_235) | ~v2_pre_topc(A_235) | v2_struct_0(A_235) | ~l1_struct_0(D_236))), inference(negUnitSimplification, [status(thm)], [c_50, c_754])).
% 3.90/1.72  tff(c_790, plain, (![A_250, D_251, D_252]: (k3_tmap_1(A_250, '#skF_2', D_251, D_252, k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_251))=k2_tmap_1(D_251, '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_251), D_252) | ~m1_pre_topc(D_252, D_251) | ~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_251), u1_struct_0(D_251), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_251)) | ~m1_pre_topc(D_252, A_250) | ~m1_pre_topc(D_251, A_250) | ~l1_pre_topc(A_250) | ~v2_pre_topc(A_250) | v2_struct_0(A_250) | ~l1_struct_0(D_251) | ~m1_pre_topc(D_252, D_251) | ~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_251), u1_struct_0(D_251), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_251)) | ~l1_pre_topc(D_251) | ~v2_pre_topc(D_251) | v2_struct_0(D_251) | ~l1_struct_0(D_251))), inference(superposition, [status(thm), theory('equality')], [c_708, c_756])).
% 3.90/1.72  tff(c_795, plain, (![A_256, D_257, D_258]: (k3_tmap_1(A_256, '#skF_2', D_257, D_258, k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_257))=k2_tmap_1(D_257, '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_257), D_258) | ~m1_pre_topc(D_258, A_256) | ~m1_pre_topc(D_257, A_256) | ~l1_pre_topc(A_256) | ~v2_pre_topc(A_256) | v2_struct_0(A_256) | ~m1_pre_topc(D_258, D_257) | ~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_257), u1_struct_0(D_257), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_257)) | ~l1_pre_topc(D_257) | ~v2_pre_topc(D_257) | v2_struct_0(D_257) | ~l1_struct_0(D_257))), inference(resolution, [status(thm)], [c_266, c_790])).
% 3.90/1.72  tff(c_799, plain, (![A_259, D_260, D_261]: (k3_tmap_1(A_259, '#skF_2', D_260, D_261, k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_260))=k2_tmap_1(D_260, '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_260), D_261) | ~m1_pre_topc(D_261, A_259) | ~m1_pre_topc(D_260, A_259) | ~l1_pre_topc(A_259) | ~v2_pre_topc(A_259) | v2_struct_0(A_259) | ~m1_pre_topc(D_261, D_260) | ~v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_260)) | ~l1_pre_topc(D_260) | ~v2_pre_topc(D_260) | v2_struct_0(D_260) | ~l1_struct_0(D_260))), inference(resolution, [status(thm)], [c_266, c_795])).
% 3.90/1.72  tff(c_803, plain, (![A_262, D_263, D_264]: (k3_tmap_1(A_262, '#skF_2', D_263, D_264, k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_263))=k2_tmap_1(D_263, '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_263), D_264) | ~m1_pre_topc(D_264, A_262) | ~m1_pre_topc(D_263, A_262) | ~l1_pre_topc(A_262) | ~v2_pre_topc(A_262) | v2_struct_0(A_262) | ~m1_pre_topc(D_264, D_263) | ~l1_pre_topc(D_263) | ~v2_pre_topc(D_263) | v2_struct_0(D_263) | ~l1_struct_0(D_263))), inference(resolution, [status(thm)], [c_259, c_799])).
% 3.90/1.72  tff(c_101, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_89])).
% 3.90/1.72  tff(c_116, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_101])).
% 3.90/1.72  tff(c_32, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.90/1.72  tff(c_120, plain, (![C_158, A_159, B_160]: (m1_pre_topc(C_158, A_159) | ~m1_pre_topc(C_158, B_160) | ~m1_pre_topc(B_160, A_159) | ~l1_pre_topc(A_159) | ~v2_pre_topc(A_159))), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.90/1.72  tff(c_131, plain, (![A_159]: (m1_pre_topc('#skF_5', A_159) | ~m1_pre_topc('#skF_4', A_159) | ~l1_pre_topc(A_159) | ~v2_pre_topc(A_159))), inference(resolution, [status(thm)], [c_30, c_120])).
% 3.90/1.72  tff(c_432, plain, (![A_204, D_201]: (k3_tmap_1(A_204, '#skF_2', '#skF_3', D_201, '#skF_6')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_201)) | ~m1_pre_topc(D_201, '#skF_3') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_201, A_204) | ~m1_pre_topc('#skF_3', A_204) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_204) | ~v2_pre_topc(A_204) | v2_struct_0(A_204))), inference(resolution, [status(thm)], [c_24, c_428])).
% 3.90/1.72  tff(c_436, plain, (![A_204, D_201]: (k3_tmap_1(A_204, '#skF_2', '#skF_3', D_201, '#skF_6')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_201)) | ~m1_pre_topc(D_201, '#skF_3') | ~m1_pre_topc(D_201, A_204) | ~m1_pre_topc('#skF_3', A_204) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_204) | ~v2_pre_topc(A_204) | v2_struct_0(A_204))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_28, c_26, c_432])).
% 3.90/1.72  tff(c_438, plain, (![A_205, D_206]: (k3_tmap_1(A_205, '#skF_2', '#skF_3', D_206, '#skF_6')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_206)) | ~m1_pre_topc(D_206, '#skF_3') | ~m1_pre_topc(D_206, A_205) | ~m1_pre_topc('#skF_3', A_205) | ~l1_pre_topc(A_205) | ~v2_pre_topc(A_205) | v2_struct_0(A_205))), inference(negUnitSimplification, [status(thm)], [c_50, c_436])).
% 3.90/1.72  tff(c_448, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5', '#skF_6') | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_438])).
% 3.90/1.72  tff(c_464, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5', '#skF_6') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_42, c_448])).
% 3.90/1.72  tff(c_465, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5', '#skF_6') | ~m1_pre_topc('#skF_5', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_56, c_464])).
% 3.90/1.72  tff(c_500, plain, (~m1_pre_topc('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_465])).
% 3.90/1.72  tff(c_503, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_131, c_500])).
% 3.90/1.72  tff(c_510, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_116, c_83, c_32, c_503])).
% 3.90/1.72  tff(c_512, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_465])).
% 3.90/1.72  tff(c_511, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_465])).
% 3.90/1.72  tff(c_44, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.90/1.72  tff(c_406, plain, (![D_191]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_191))=k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_191) | ~m1_pre_topc(D_191, '#skF_3') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_24, c_402])).
% 3.90/1.72  tff(c_410, plain, (![D_191]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_191))=k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_191) | ~m1_pre_topc(D_191, '#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_83, c_48, c_46, c_28, c_26, c_406])).
% 3.90/1.72  tff(c_411, plain, (![D_191]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_191))=k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_191) | ~m1_pre_topc(D_191, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_44, c_50, c_410])).
% 3.90/1.72  tff(c_602, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5', '#skF_6')=k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_511, c_411])).
% 3.90/1.72  tff(c_609, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5', '#skF_6')=k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_512, c_602])).
% 3.90/1.72  tff(c_450, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6') | ~m1_pre_topc('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_438])).
% 3.90/1.72  tff(c_468, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_42, c_32, c_450])).
% 3.90/1.72  tff(c_469, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_56, c_468])).
% 3.90/1.72  tff(c_482, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6')=k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_469, c_411])).
% 3.90/1.72  tff(c_489, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6')=k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_482])).
% 3.90/1.72  tff(c_22, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6')), k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.90/1.72  tff(c_494, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4')), k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_489, c_22])).
% 3.90/1.72  tff(c_718, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_5', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4')), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_609, c_494])).
% 3.90/1.72  tff(c_812, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), '#skF_5'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_5')) | ~m1_pre_topc('#skF_5', '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~m1_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_803, c_718])).
% 3.90/1.72  tff(c_825, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), '#skF_5'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_5')) | v2_struct_0('#skF_1') | v2_struct_0('#skF_4') | ~l1_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_80, c_30, c_54, c_52, c_38, c_34, c_812])).
% 3.90/1.72  tff(c_826, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), '#skF_5'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_5')) | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_40, c_56, c_825])).
% 3.90/1.72  tff(c_831, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_826])).
% 3.90/1.72  tff(c_843, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_4, c_831])).
% 3.90/1.72  tff(c_847, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_843])).
% 3.90/1.72  tff(c_849, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_826])).
% 3.90/1.72  tff(c_18, plain, (![A_58, E_88, B_74, D_86, C_82]: (r2_funct_2(u1_struct_0(C_82), u1_struct_0(B_74), k3_tmap_1(A_58, B_74, D_86, C_82, k2_tmap_1(A_58, B_74, E_88, D_86)), k2_tmap_1(A_58, B_74, E_88, C_82)) | ~m1_pre_topc(C_82, D_86) | ~m1_subset_1(E_88, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_58), u1_struct_0(B_74)))) | ~v1_funct_2(E_88, u1_struct_0(A_58), u1_struct_0(B_74)) | ~v1_funct_1(E_88) | ~m1_pre_topc(D_86, A_58) | v2_struct_0(D_86) | ~m1_pre_topc(C_82, A_58) | v2_struct_0(C_82) | ~l1_pre_topc(B_74) | ~v2_pre_topc(B_74) | v2_struct_0(B_74) | ~l1_pre_topc(A_58) | ~v2_pre_topc(A_58) | v2_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.90/1.72  tff(c_816, plain, (![D_264, D_263]: (r2_funct_2(u1_struct_0(D_264), u1_struct_0('#skF_2'), k2_tmap_1(D_263, '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_263), D_264), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_264)) | ~m1_pre_topc(D_264, D_263) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_263, '#skF_3') | v2_struct_0(D_263) | ~m1_pre_topc(D_264, '#skF_3') | v2_struct_0(D_264) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(D_264, '#skF_3') | ~m1_pre_topc(D_263, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(D_264, D_263) | ~l1_pre_topc(D_263) | ~v2_pre_topc(D_263) | v2_struct_0(D_263) | ~l1_struct_0(D_263))), inference(superposition, [status(thm), theory('equality')], [c_803, c_18])).
% 3.90/1.72  tff(c_828, plain, (![D_264, D_263]: (r2_funct_2(u1_struct_0(D_264), u1_struct_0('#skF_2'), k2_tmap_1(D_263, '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_263), D_264), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_264)) | v2_struct_0(D_264) | v2_struct_0('#skF_2') | ~m1_pre_topc(D_264, '#skF_3') | ~m1_pre_topc(D_263, '#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(D_264, D_263) | ~l1_pre_topc(D_263) | ~v2_pre_topc(D_263) | v2_struct_0(D_263) | ~l1_struct_0(D_263))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_83, c_116, c_83, c_48, c_46, c_28, c_26, c_24, c_816])).
% 3.90/1.72  tff(c_850, plain, (![D_271, D_272]: (r2_funct_2(u1_struct_0(D_271), u1_struct_0('#skF_2'), k2_tmap_1(D_272, '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_272), D_271), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_271)) | v2_struct_0(D_271) | ~m1_pre_topc(D_271, '#skF_3') | ~m1_pre_topc(D_272, '#skF_3') | ~m1_pre_topc(D_271, D_272) | ~l1_pre_topc(D_272) | ~v2_pre_topc(D_272) | v2_struct_0(D_272) | ~l1_struct_0(D_272))), inference(negUnitSimplification, [status(thm)], [c_44, c_50, c_828])).
% 3.90/1.72  tff(c_848, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_4'), '#skF_5'), k2_tmap_1('#skF_3', '#skF_2', '#skF_6', '#skF_5'))), inference(splitRight, [status(thm)], [c_826])).
% 3.90/1.72  tff(c_853, plain, (v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_850, c_848])).
% 3.90/1.72  tff(c_856, plain, (v2_struct_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_849, c_113, c_80, c_30, c_32, c_512, c_853])).
% 3.90/1.72  tff(c_858, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_36, c_856])).
% 3.90/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.90/1.72  
% 3.90/1.72  Inference rules
% 3.90/1.72  ----------------------
% 3.90/1.72  #Ref     : 0
% 3.90/1.72  #Sup     : 158
% 3.90/1.72  #Fact    : 0
% 3.90/1.72  #Define  : 0
% 3.90/1.72  #Split   : 9
% 3.90/1.72  #Chain   : 0
% 3.90/1.72  #Close   : 0
% 3.90/1.72  
% 3.90/1.72  Ordering : KBO
% 3.90/1.73  
% 3.90/1.73  Simplification rules
% 3.90/1.73  ----------------------
% 3.90/1.73  #Subsume      : 37
% 3.90/1.73  #Demod        : 329
% 3.90/1.73  #Tautology    : 64
% 3.90/1.73  #SimpNegUnit  : 14
% 3.90/1.73  #BackRed      : 3
% 3.90/1.73  
% 3.90/1.73  #Partial instantiations: 0
% 3.90/1.73  #Strategies tried      : 1
% 3.90/1.73  
% 3.90/1.73  Timing (in seconds)
% 3.90/1.73  ----------------------
% 3.90/1.73  Preprocessing        : 0.39
% 3.90/1.73  Parsing              : 0.19
% 3.90/1.73  CNF conversion       : 0.06
% 3.90/1.73  Main loop            : 0.52
% 3.90/1.73  Inferencing          : 0.19
% 3.90/1.73  Reduction            : 0.16
% 3.90/1.73  Demodulation         : 0.11
% 3.90/1.73  BG Simplification    : 0.03
% 3.90/1.73  Subsumption          : 0.12
% 3.90/1.73  Abstraction          : 0.02
% 3.90/1.73  MUC search           : 0.00
% 3.90/1.73  Cooper               : 0.00
% 3.90/1.73  Total                : 0.97
% 3.90/1.73  Index Insertion      : 0.00
% 3.90/1.73  Index Deletion       : 0.00
% 3.90/1.73  Index Matching       : 0.00
% 3.90/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
