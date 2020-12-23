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
% DateTime   : Thu Dec  3 10:27:44 EST 2020

% Result     : Theorem 3.08s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 246 expanded)
%              Number of leaves         :   29 ( 109 expanded)
%              Depth                    :   13
%              Number of atoms          :  350 (1921 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_210,negated_conjecture,(
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
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                          & v5_pre_topc(E,C,B)
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                       => ( m1_pre_topc(D,C)
                         => ( v1_funct_1(k3_tmap_1(A,B,C,D,E))
                            & v1_funct_2(k3_tmap_1(A,B,C,D,E),u1_struct_0(D),u1_struct_0(B))
                            & v5_pre_topc(k3_tmap_1(A,B,C,D,E),D,B)
                            & m1_subset_1(k3_tmap_1(A,B,C,D,E),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_tmap_1)).

tff(f_34,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_163,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & v2_pre_topc(B)
        & l1_pre_topc(B)
        & v1_funct_1(C)
        & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
        & v5_pre_topc(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B))))
        & ~ v2_struct_0(D)
        & m1_pre_topc(D,A) )
     => ( v1_funct_1(k2_tmap_1(A,B,C,D))
        & v1_funct_2(k2_tmap_1(A,B,C,D),u1_struct_0(D),u1_struct_0(B))
        & v5_pre_topc(k2_tmap_1(A,B,C,D),D,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tmap_1)).

tff(f_100,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

tff(f_68,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_130,axiom,(
    ! [A,B,C,D,E] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & v2_pre_topc(B)
        & l1_pre_topc(B)
        & m1_pre_topc(C,A)
        & m1_pre_topc(D,A)
        & v1_funct_1(E)
        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
     => ( v1_funct_1(k3_tmap_1(A,B,C,D,E))
        & v1_funct_2(k3_tmap_1(A,B,C,D,E),u1_struct_0(D),u1_struct_0(B))
        & m1_subset_1(k3_tmap_1(A,B,C,D,E),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_tmap_1)).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_24,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_50,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_48,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_38,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_112,plain,(
    ! [B_99,A_100] :
      ( v2_pre_topc(B_99)
      | ~ m1_pre_topc(B_99,A_100)
      | ~ l1_pre_topc(A_100)
      | ~ v2_pre_topc(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_121,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_112])).

tff(c_130,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_121])).

tff(c_53,plain,(
    ! [B_88,A_89] :
      ( l1_pre_topc(B_88)
      | ~ m1_pre_topc(B_88,A_89)
      | ~ l1_pre_topc(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_62,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_53])).

tff(c_69,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_62])).

tff(c_44,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_42,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_32,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_30,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_28,plain,(
    v5_pre_topc('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_26,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_374,plain,(
    ! [A_193,B_194,C_195,D_196] :
      ( v5_pre_topc(k2_tmap_1(A_193,B_194,C_195,D_196),D_196,B_194)
      | ~ m1_pre_topc(D_196,A_193)
      | v2_struct_0(D_196)
      | ~ m1_subset_1(C_195,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_193),u1_struct_0(B_194))))
      | ~ v5_pre_topc(C_195,A_193,B_194)
      | ~ v1_funct_2(C_195,u1_struct_0(A_193),u1_struct_0(B_194))
      | ~ v1_funct_1(C_195)
      | ~ l1_pre_topc(B_194)
      | ~ v2_pre_topc(B_194)
      | v2_struct_0(B_194)
      | ~ l1_pre_topc(A_193)
      | ~ v2_pre_topc(A_193)
      | v2_struct_0(A_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_378,plain,(
    ! [D_196] :
      ( v5_pre_topc(k2_tmap_1('#skF_3','#skF_2','#skF_5',D_196),D_196,'#skF_2')
      | ~ m1_pre_topc(D_196,'#skF_3')
      | v2_struct_0(D_196)
      | ~ v5_pre_topc('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_374])).

tff(c_385,plain,(
    ! [D_196] :
      ( v5_pre_topc(k2_tmap_1('#skF_3','#skF_2','#skF_5',D_196),D_196,'#skF_2')
      | ~ m1_pre_topc(D_196,'#skF_3')
      | v2_struct_0(D_196)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_69,c_44,c_42,c_32,c_30,c_28,c_378])).

tff(c_386,plain,(
    ! [D_196] :
      ( v5_pre_topc(k2_tmap_1('#skF_3','#skF_2','#skF_5',D_196),D_196,'#skF_2')
      | ~ m1_pre_topc(D_196,'#skF_3')
      | v2_struct_0(D_196) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_46,c_385])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_34,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_421,plain,(
    ! [E_211,A_209,B_210,D_208,C_212] :
      ( k3_tmap_1(A_209,B_210,C_212,D_208,E_211) = k2_partfun1(u1_struct_0(C_212),u1_struct_0(B_210),E_211,u1_struct_0(D_208))
      | ~ m1_pre_topc(D_208,C_212)
      | ~ m1_subset_1(E_211,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_212),u1_struct_0(B_210))))
      | ~ v1_funct_2(E_211,u1_struct_0(C_212),u1_struct_0(B_210))
      | ~ v1_funct_1(E_211)
      | ~ m1_pre_topc(D_208,A_209)
      | ~ m1_pre_topc(C_212,A_209)
      | ~ l1_pre_topc(B_210)
      | ~ v2_pre_topc(B_210)
      | v2_struct_0(B_210)
      | ~ l1_pre_topc(A_209)
      | ~ v2_pre_topc(A_209)
      | v2_struct_0(A_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_427,plain,(
    ! [A_209,D_208] :
      ( k3_tmap_1(A_209,'#skF_2','#skF_3',D_208,'#skF_5') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_208))
      | ~ m1_pre_topc(D_208,'#skF_3')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_208,A_209)
      | ~ m1_pre_topc('#skF_3',A_209)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_209)
      | ~ v2_pre_topc(A_209)
      | v2_struct_0(A_209) ) ),
    inference(resolution,[status(thm)],[c_26,c_421])).

tff(c_435,plain,(
    ! [A_209,D_208] :
      ( k3_tmap_1(A_209,'#skF_2','#skF_3',D_208,'#skF_5') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_208))
      | ~ m1_pre_topc(D_208,'#skF_3')
      | ~ m1_pre_topc(D_208,A_209)
      | ~ m1_pre_topc('#skF_3',A_209)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_209)
      | ~ v2_pre_topc(A_209)
      | v2_struct_0(A_209) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_32,c_30,c_427])).

tff(c_437,plain,(
    ! [A_213,D_214] :
      ( k3_tmap_1(A_213,'#skF_2','#skF_3',D_214,'#skF_5') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_214))
      | ~ m1_pre_topc(D_214,'#skF_3')
      | ~ m1_pre_topc(D_214,A_213)
      | ~ m1_pre_topc('#skF_3',A_213)
      | ~ l1_pre_topc(A_213)
      | ~ v2_pre_topc(A_213)
      | v2_struct_0(A_213) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_435])).

tff(c_441,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_437])).

tff(c_450,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_38,c_24,c_441])).

tff(c_451,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_450])).

tff(c_328,plain,(
    ! [A_178,B_179,C_180,D_181] :
      ( k2_partfun1(u1_struct_0(A_178),u1_struct_0(B_179),C_180,u1_struct_0(D_181)) = k2_tmap_1(A_178,B_179,C_180,D_181)
      | ~ m1_pre_topc(D_181,A_178)
      | ~ m1_subset_1(C_180,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_178),u1_struct_0(B_179))))
      | ~ v1_funct_2(C_180,u1_struct_0(A_178),u1_struct_0(B_179))
      | ~ v1_funct_1(C_180)
      | ~ l1_pre_topc(B_179)
      | ~ v2_pre_topc(B_179)
      | v2_struct_0(B_179)
      | ~ l1_pre_topc(A_178)
      | ~ v2_pre_topc(A_178)
      | v2_struct_0(A_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_332,plain,(
    ! [D_181] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_181)) = k2_tmap_1('#skF_3','#skF_2','#skF_5',D_181)
      | ~ m1_pre_topc(D_181,'#skF_3')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_328])).

tff(c_339,plain,(
    ! [D_181] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_181)) = k2_tmap_1('#skF_3','#skF_2','#skF_5',D_181)
      | ~ m1_pre_topc(D_181,'#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_69,c_44,c_42,c_32,c_30,c_332])).

tff(c_340,plain,(
    ! [D_181] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_181)) = k2_tmap_1('#skF_3','#skF_2','#skF_5',D_181)
      | ~ m1_pre_topc(D_181,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_46,c_339])).

tff(c_459,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_451,c_340])).

tff(c_466,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_459])).

tff(c_275,plain,(
    ! [B_161,D_160,E_159,A_158,C_157] :
      ( v1_funct_2(k3_tmap_1(A_158,B_161,C_157,D_160,E_159),u1_struct_0(D_160),u1_struct_0(B_161))
      | ~ m1_subset_1(E_159,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_157),u1_struct_0(B_161))))
      | ~ v1_funct_2(E_159,u1_struct_0(C_157),u1_struct_0(B_161))
      | ~ v1_funct_1(E_159)
      | ~ m1_pre_topc(D_160,A_158)
      | ~ m1_pre_topc(C_157,A_158)
      | ~ l1_pre_topc(B_161)
      | ~ v2_pre_topc(B_161)
      | v2_struct_0(B_161)
      | ~ l1_pre_topc(A_158)
      | ~ v2_pre_topc(A_158)
      | v2_struct_0(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_279,plain,(
    ! [A_158,D_160] :
      ( v1_funct_2(k3_tmap_1(A_158,'#skF_2','#skF_3',D_160,'#skF_5'),u1_struct_0(D_160),u1_struct_0('#skF_2'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_160,A_158)
      | ~ m1_pre_topc('#skF_3',A_158)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_158)
      | ~ v2_pre_topc(A_158)
      | v2_struct_0(A_158) ) ),
    inference(resolution,[status(thm)],[c_26,c_275])).

tff(c_286,plain,(
    ! [A_158,D_160] :
      ( v1_funct_2(k3_tmap_1(A_158,'#skF_2','#skF_3',D_160,'#skF_5'),u1_struct_0(D_160),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_160,A_158)
      | ~ m1_pre_topc('#skF_3',A_158)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_158)
      | ~ v2_pre_topc(A_158)
      | v2_struct_0(A_158) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_32,c_30,c_279])).

tff(c_288,plain,(
    ! [A_162,D_163] :
      ( v1_funct_2(k3_tmap_1(A_162,'#skF_2','#skF_3',D_163,'#skF_5'),u1_struct_0(D_163),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_163,A_162)
      | ~ m1_pre_topc('#skF_3',A_162)
      | ~ l1_pre_topc(A_162)
      | ~ v2_pre_topc(A_162)
      | v2_struct_0(A_162) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_286])).

tff(c_182,plain,(
    ! [E_132,D_133,C_130,A_131,B_134] :
      ( m1_subset_1(k3_tmap_1(A_131,B_134,C_130,D_133,E_132),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_133),u1_struct_0(B_134))))
      | ~ m1_subset_1(E_132,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_130),u1_struct_0(B_134))))
      | ~ v1_funct_2(E_132,u1_struct_0(C_130),u1_struct_0(B_134))
      | ~ v1_funct_1(E_132)
      | ~ m1_pre_topc(D_133,A_131)
      | ~ m1_pre_topc(C_130,A_131)
      | ~ l1_pre_topc(B_134)
      | ~ v2_pre_topc(B_134)
      | v2_struct_0(B_134)
      | ~ l1_pre_topc(A_131)
      | ~ v2_pre_topc(A_131)
      | v2_struct_0(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_94,plain,(
    ! [C_92,E_94,D_95,B_96,A_93] :
      ( v1_funct_1(k3_tmap_1(A_93,B_96,C_92,D_95,E_94))
      | ~ m1_subset_1(E_94,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_92),u1_struct_0(B_96))))
      | ~ v1_funct_2(E_94,u1_struct_0(C_92),u1_struct_0(B_96))
      | ~ v1_funct_1(E_94)
      | ~ m1_pre_topc(D_95,A_93)
      | ~ m1_pre_topc(C_92,A_93)
      | ~ l1_pre_topc(B_96)
      | ~ v2_pre_topc(B_96)
      | v2_struct_0(B_96)
      | ~ l1_pre_topc(A_93)
      | ~ v2_pre_topc(A_93)
      | v2_struct_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_96,plain,(
    ! [A_93,D_95] :
      ( v1_funct_1(k3_tmap_1(A_93,'#skF_2','#skF_3',D_95,'#skF_5'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_95,A_93)
      | ~ m1_pre_topc('#skF_3',A_93)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_93)
      | ~ v2_pre_topc(A_93)
      | v2_struct_0(A_93) ) ),
    inference(resolution,[status(thm)],[c_26,c_94])).

tff(c_99,plain,(
    ! [A_93,D_95] :
      ( v1_funct_1(k3_tmap_1(A_93,'#skF_2','#skF_3',D_95,'#skF_5'))
      | ~ m1_pre_topc(D_95,A_93)
      | ~ m1_pre_topc('#skF_3',A_93)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_93)
      | ~ v2_pre_topc(A_93)
      | v2_struct_0(A_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_32,c_30,c_96])).

tff(c_101,plain,(
    ! [A_97,D_98] :
      ( v1_funct_1(k3_tmap_1(A_97,'#skF_2','#skF_3',D_98,'#skF_5'))
      | ~ m1_pre_topc(D_98,A_97)
      | ~ m1_pre_topc('#skF_3',A_97)
      | ~ l1_pre_topc(A_97)
      | ~ v2_pre_topc(A_97)
      | v2_struct_0(A_97) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_99])).

tff(c_22,plain,
    ( ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2')
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_72,plain,(
    ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_104,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_101,c_72])).

tff(c_107,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_38,c_34,c_104])).

tff(c_109,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_107])).

tff(c_110,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2')
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_131,plain,(
    ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_195,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_182,c_131])).

tff(c_203,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_44,c_42,c_38,c_34,c_32,c_30,c_26,c_195])).

tff(c_205,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_46,c_203])).

tff(c_206,plain,
    ( ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2')
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_210,plain,(
    ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_206])).

tff(c_291,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_288,c_210])).

tff(c_294,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_38,c_34,c_291])).

tff(c_296,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_294])).

tff(c_297,plain,(
    ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_206])).

tff(c_475,plain,(
    ~ v5_pre_topc(k2_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4'),'#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_466,c_297])).

tff(c_525,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_386,c_475])).

tff(c_528,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_525])).

tff(c_530,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_528])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:32:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.08/1.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.54  
% 3.08/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.55  %$ v5_pre_topc > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.08/1.55  
% 3.08/1.55  %Foreground sorts:
% 3.08/1.55  
% 3.08/1.55  
% 3.08/1.55  %Background operators:
% 3.08/1.55  
% 3.08/1.55  
% 3.08/1.55  %Foreground operators:
% 3.08/1.55  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.08/1.55  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.08/1.55  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.08/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.08/1.55  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.08/1.55  tff('#skF_5', type, '#skF_5': $i).
% 3.08/1.55  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.08/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.08/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.08/1.55  tff('#skF_1', type, '#skF_1': $i).
% 3.08/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.08/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.08/1.55  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.08/1.55  tff('#skF_4', type, '#skF_4': $i).
% 3.08/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.08/1.55  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 3.08/1.55  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.08/1.55  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.08/1.55  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.08/1.55  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.08/1.55  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.08/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.08/1.55  
% 3.39/1.56  tff(f_210, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: ((((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & v5_pre_topc(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (((v1_funct_1(k3_tmap_1(A, B, C, D, E)) & v1_funct_2(k3_tmap_1(A, B, C, D, E), u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(k3_tmap_1(A, B, C, D, E), D, B)) & m1_subset_1(k3_tmap_1(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B)))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t89_tmap_1)).
% 3.39/1.56  tff(f_34, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.39/1.56  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.39/1.56  tff(f_163, axiom, (![A, B, C, D]: ((((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & v1_funct_1(C)) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) & ~v2_struct_0(D)) & m1_pre_topc(D, A)) => ((v1_funct_1(k2_tmap_1(A, B, C, D)) & v1_funct_2(k2_tmap_1(A, B, C, D), u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(k2_tmap_1(A, B, C, D), D, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_tmap_1)).
% 3.39/1.56  tff(f_100, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 3.39/1.56  tff(f_68, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 3.39/1.56  tff(f_130, axiom, (![A, B, C, D, E]: (((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & m1_pre_topc(C, A)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((v1_funct_1(k3_tmap_1(A, B, C, D, E)) & v1_funct_2(k3_tmap_1(A, B, C, D, E), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k3_tmap_1(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 3.39/1.56  tff(c_36, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.39/1.56  tff(c_24, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.39/1.56  tff(c_40, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.39/1.56  tff(c_46, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.39/1.56  tff(c_50, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.39/1.56  tff(c_48, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.39/1.56  tff(c_38, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.39/1.56  tff(c_112, plain, (![B_99, A_100]: (v2_pre_topc(B_99) | ~m1_pre_topc(B_99, A_100) | ~l1_pre_topc(A_100) | ~v2_pre_topc(A_100))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.39/1.56  tff(c_121, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_112])).
% 3.39/1.56  tff(c_130, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_121])).
% 3.39/1.56  tff(c_53, plain, (![B_88, A_89]: (l1_pre_topc(B_88) | ~m1_pre_topc(B_88, A_89) | ~l1_pre_topc(A_89))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.39/1.56  tff(c_62, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_53])).
% 3.39/1.56  tff(c_69, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_62])).
% 3.39/1.56  tff(c_44, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.39/1.56  tff(c_42, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.39/1.56  tff(c_32, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.39/1.56  tff(c_30, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.39/1.56  tff(c_28, plain, (v5_pre_topc('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.39/1.56  tff(c_26, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.39/1.56  tff(c_374, plain, (![A_193, B_194, C_195, D_196]: (v5_pre_topc(k2_tmap_1(A_193, B_194, C_195, D_196), D_196, B_194) | ~m1_pre_topc(D_196, A_193) | v2_struct_0(D_196) | ~m1_subset_1(C_195, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_193), u1_struct_0(B_194)))) | ~v5_pre_topc(C_195, A_193, B_194) | ~v1_funct_2(C_195, u1_struct_0(A_193), u1_struct_0(B_194)) | ~v1_funct_1(C_195) | ~l1_pre_topc(B_194) | ~v2_pre_topc(B_194) | v2_struct_0(B_194) | ~l1_pre_topc(A_193) | ~v2_pre_topc(A_193) | v2_struct_0(A_193))), inference(cnfTransformation, [status(thm)], [f_163])).
% 3.39/1.56  tff(c_378, plain, (![D_196]: (v5_pre_topc(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_196), D_196, '#skF_2') | ~m1_pre_topc(D_196, '#skF_3') | v2_struct_0(D_196) | ~v5_pre_topc('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_26, c_374])).
% 3.39/1.56  tff(c_385, plain, (![D_196]: (v5_pre_topc(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_196), D_196, '#skF_2') | ~m1_pre_topc(D_196, '#skF_3') | v2_struct_0(D_196) | v2_struct_0('#skF_2') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_69, c_44, c_42, c_32, c_30, c_28, c_378])).
% 3.39/1.56  tff(c_386, plain, (![D_196]: (v5_pre_topc(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_196), D_196, '#skF_2') | ~m1_pre_topc(D_196, '#skF_3') | v2_struct_0(D_196))), inference(negUnitSimplification, [status(thm)], [c_40, c_46, c_385])).
% 3.39/1.56  tff(c_52, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.39/1.56  tff(c_34, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.39/1.56  tff(c_421, plain, (![E_211, A_209, B_210, D_208, C_212]: (k3_tmap_1(A_209, B_210, C_212, D_208, E_211)=k2_partfun1(u1_struct_0(C_212), u1_struct_0(B_210), E_211, u1_struct_0(D_208)) | ~m1_pre_topc(D_208, C_212) | ~m1_subset_1(E_211, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_212), u1_struct_0(B_210)))) | ~v1_funct_2(E_211, u1_struct_0(C_212), u1_struct_0(B_210)) | ~v1_funct_1(E_211) | ~m1_pre_topc(D_208, A_209) | ~m1_pre_topc(C_212, A_209) | ~l1_pre_topc(B_210) | ~v2_pre_topc(B_210) | v2_struct_0(B_210) | ~l1_pre_topc(A_209) | ~v2_pre_topc(A_209) | v2_struct_0(A_209))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.39/1.56  tff(c_427, plain, (![A_209, D_208]: (k3_tmap_1(A_209, '#skF_2', '#skF_3', D_208, '#skF_5')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_208)) | ~m1_pre_topc(D_208, '#skF_3') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_208, A_209) | ~m1_pre_topc('#skF_3', A_209) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_209) | ~v2_pre_topc(A_209) | v2_struct_0(A_209))), inference(resolution, [status(thm)], [c_26, c_421])).
% 3.39/1.56  tff(c_435, plain, (![A_209, D_208]: (k3_tmap_1(A_209, '#skF_2', '#skF_3', D_208, '#skF_5')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_208)) | ~m1_pre_topc(D_208, '#skF_3') | ~m1_pre_topc(D_208, A_209) | ~m1_pre_topc('#skF_3', A_209) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_209) | ~v2_pre_topc(A_209) | v2_struct_0(A_209))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_32, c_30, c_427])).
% 3.39/1.56  tff(c_437, plain, (![A_213, D_214]: (k3_tmap_1(A_213, '#skF_2', '#skF_3', D_214, '#skF_5')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_214)) | ~m1_pre_topc(D_214, '#skF_3') | ~m1_pre_topc(D_214, A_213) | ~m1_pre_topc('#skF_3', A_213) | ~l1_pre_topc(A_213) | ~v2_pre_topc(A_213) | v2_struct_0(A_213))), inference(negUnitSimplification, [status(thm)], [c_46, c_435])).
% 3.39/1.56  tff(c_441, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_437])).
% 3.39/1.56  tff(c_450, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_38, c_24, c_441])).
% 3.39/1.56  tff(c_451, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_52, c_450])).
% 3.39/1.56  tff(c_328, plain, (![A_178, B_179, C_180, D_181]: (k2_partfun1(u1_struct_0(A_178), u1_struct_0(B_179), C_180, u1_struct_0(D_181))=k2_tmap_1(A_178, B_179, C_180, D_181) | ~m1_pre_topc(D_181, A_178) | ~m1_subset_1(C_180, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_178), u1_struct_0(B_179)))) | ~v1_funct_2(C_180, u1_struct_0(A_178), u1_struct_0(B_179)) | ~v1_funct_1(C_180) | ~l1_pre_topc(B_179) | ~v2_pre_topc(B_179) | v2_struct_0(B_179) | ~l1_pre_topc(A_178) | ~v2_pre_topc(A_178) | v2_struct_0(A_178))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.39/1.56  tff(c_332, plain, (![D_181]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_181))=k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_181) | ~m1_pre_topc(D_181, '#skF_3') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_26, c_328])).
% 3.39/1.56  tff(c_339, plain, (![D_181]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_181))=k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_181) | ~m1_pre_topc(D_181, '#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_69, c_44, c_42, c_32, c_30, c_332])).
% 3.39/1.56  tff(c_340, plain, (![D_181]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_181))=k2_tmap_1('#skF_3', '#skF_2', '#skF_5', D_181) | ~m1_pre_topc(D_181, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_40, c_46, c_339])).
% 3.39/1.56  tff(c_459, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_451, c_340])).
% 3.39/1.56  tff(c_466, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_459])).
% 3.39/1.56  tff(c_275, plain, (![B_161, D_160, E_159, A_158, C_157]: (v1_funct_2(k3_tmap_1(A_158, B_161, C_157, D_160, E_159), u1_struct_0(D_160), u1_struct_0(B_161)) | ~m1_subset_1(E_159, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_157), u1_struct_0(B_161)))) | ~v1_funct_2(E_159, u1_struct_0(C_157), u1_struct_0(B_161)) | ~v1_funct_1(E_159) | ~m1_pre_topc(D_160, A_158) | ~m1_pre_topc(C_157, A_158) | ~l1_pre_topc(B_161) | ~v2_pre_topc(B_161) | v2_struct_0(B_161) | ~l1_pre_topc(A_158) | ~v2_pre_topc(A_158) | v2_struct_0(A_158))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.39/1.56  tff(c_279, plain, (![A_158, D_160]: (v1_funct_2(k3_tmap_1(A_158, '#skF_2', '#skF_3', D_160, '#skF_5'), u1_struct_0(D_160), u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_160, A_158) | ~m1_pre_topc('#skF_3', A_158) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_158) | ~v2_pre_topc(A_158) | v2_struct_0(A_158))), inference(resolution, [status(thm)], [c_26, c_275])).
% 3.39/1.56  tff(c_286, plain, (![A_158, D_160]: (v1_funct_2(k3_tmap_1(A_158, '#skF_2', '#skF_3', D_160, '#skF_5'), u1_struct_0(D_160), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_160, A_158) | ~m1_pre_topc('#skF_3', A_158) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_158) | ~v2_pre_topc(A_158) | v2_struct_0(A_158))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_32, c_30, c_279])).
% 3.39/1.56  tff(c_288, plain, (![A_162, D_163]: (v1_funct_2(k3_tmap_1(A_162, '#skF_2', '#skF_3', D_163, '#skF_5'), u1_struct_0(D_163), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_163, A_162) | ~m1_pre_topc('#skF_3', A_162) | ~l1_pre_topc(A_162) | ~v2_pre_topc(A_162) | v2_struct_0(A_162))), inference(negUnitSimplification, [status(thm)], [c_46, c_286])).
% 3.39/1.56  tff(c_182, plain, (![E_132, D_133, C_130, A_131, B_134]: (m1_subset_1(k3_tmap_1(A_131, B_134, C_130, D_133, E_132), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_133), u1_struct_0(B_134)))) | ~m1_subset_1(E_132, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_130), u1_struct_0(B_134)))) | ~v1_funct_2(E_132, u1_struct_0(C_130), u1_struct_0(B_134)) | ~v1_funct_1(E_132) | ~m1_pre_topc(D_133, A_131) | ~m1_pre_topc(C_130, A_131) | ~l1_pre_topc(B_134) | ~v2_pre_topc(B_134) | v2_struct_0(B_134) | ~l1_pre_topc(A_131) | ~v2_pre_topc(A_131) | v2_struct_0(A_131))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.39/1.56  tff(c_94, plain, (![C_92, E_94, D_95, B_96, A_93]: (v1_funct_1(k3_tmap_1(A_93, B_96, C_92, D_95, E_94)) | ~m1_subset_1(E_94, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_92), u1_struct_0(B_96)))) | ~v1_funct_2(E_94, u1_struct_0(C_92), u1_struct_0(B_96)) | ~v1_funct_1(E_94) | ~m1_pre_topc(D_95, A_93) | ~m1_pre_topc(C_92, A_93) | ~l1_pre_topc(B_96) | ~v2_pre_topc(B_96) | v2_struct_0(B_96) | ~l1_pre_topc(A_93) | ~v2_pre_topc(A_93) | v2_struct_0(A_93))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.39/1.56  tff(c_96, plain, (![A_93, D_95]: (v1_funct_1(k3_tmap_1(A_93, '#skF_2', '#skF_3', D_95, '#skF_5')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_95, A_93) | ~m1_pre_topc('#skF_3', A_93) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_93) | ~v2_pre_topc(A_93) | v2_struct_0(A_93))), inference(resolution, [status(thm)], [c_26, c_94])).
% 3.39/1.56  tff(c_99, plain, (![A_93, D_95]: (v1_funct_1(k3_tmap_1(A_93, '#skF_2', '#skF_3', D_95, '#skF_5')) | ~m1_pre_topc(D_95, A_93) | ~m1_pre_topc('#skF_3', A_93) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_93) | ~v2_pre_topc(A_93) | v2_struct_0(A_93))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_32, c_30, c_96])).
% 3.39/1.56  tff(c_101, plain, (![A_97, D_98]: (v1_funct_1(k3_tmap_1(A_97, '#skF_2', '#skF_3', D_98, '#skF_5')) | ~m1_pre_topc(D_98, A_97) | ~m1_pre_topc('#skF_3', A_97) | ~l1_pre_topc(A_97) | ~v2_pre_topc(A_97) | v2_struct_0(A_97))), inference(negUnitSimplification, [status(thm)], [c_46, c_99])).
% 3.39/1.57  tff(c_22, plain, (~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.39/1.57  tff(c_72, plain, (~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_22])).
% 3.39/1.57  tff(c_104, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_101, c_72])).
% 3.39/1.57  tff(c_107, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_38, c_34, c_104])).
% 3.39/1.57  tff(c_109, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_107])).
% 3.39/1.57  tff(c_110, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2') | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_22])).
% 3.39/1.57  tff(c_131, plain, (~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_110])).
% 3.39/1.57  tff(c_195, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_182, c_131])).
% 3.39/1.57  tff(c_203, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_44, c_42, c_38, c_34, c_32, c_30, c_26, c_195])).
% 3.39/1.57  tff(c_205, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_46, c_203])).
% 3.39/1.57  tff(c_206, plain, (~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_110])).
% 3.39/1.57  tff(c_210, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_206])).
% 3.39/1.57  tff(c_291, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_288, c_210])).
% 3.39/1.57  tff(c_294, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_38, c_34, c_291])).
% 3.39/1.57  tff(c_296, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_294])).
% 3.39/1.57  tff(c_297, plain, (~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_206])).
% 3.39/1.57  tff(c_475, plain, (~v5_pre_topc(k2_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_466, c_297])).
% 3.39/1.57  tff(c_525, plain, (~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_386, c_475])).
% 3.39/1.57  tff(c_528, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_525])).
% 3.39/1.57  tff(c_530, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_528])).
% 3.39/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.39/1.57  
% 3.39/1.57  Inference rules
% 3.39/1.57  ----------------------
% 3.39/1.57  #Ref     : 0
% 3.39/1.57  #Sup     : 80
% 3.39/1.57  #Fact    : 0
% 3.39/1.57  #Define  : 0
% 3.39/1.57  #Split   : 3
% 3.39/1.57  #Chain   : 0
% 3.39/1.57  #Close   : 0
% 3.39/1.57  
% 3.39/1.57  Ordering : KBO
% 3.39/1.57  
% 3.39/1.57  Simplification rules
% 3.39/1.57  ----------------------
% 3.39/1.57  #Subsume      : 8
% 3.39/1.57  #Demod        : 238
% 3.39/1.57  #Tautology    : 19
% 3.39/1.57  #SimpNegUnit  : 41
% 3.39/1.57  #BackRed      : 8
% 3.39/1.57  
% 3.39/1.57  #Partial instantiations: 0
% 3.39/1.57  #Strategies tried      : 1
% 3.39/1.57  
% 3.39/1.57  Timing (in seconds)
% 3.39/1.57  ----------------------
% 3.47/1.57  Preprocessing        : 0.38
% 3.47/1.57  Parsing              : 0.21
% 3.47/1.57  CNF conversion       : 0.04
% 3.47/1.57  Main loop            : 0.36
% 3.47/1.57  Inferencing          : 0.14
% 3.47/1.57  Reduction            : 0.11
% 3.47/1.57  Demodulation         : 0.08
% 3.47/1.57  BG Simplification    : 0.02
% 3.47/1.57  Subsumption          : 0.07
% 3.47/1.57  Abstraction          : 0.02
% 3.47/1.57  MUC search           : 0.00
% 3.47/1.57  Cooper               : 0.00
% 3.47/1.57  Total                : 0.77
% 3.47/1.57  Index Insertion      : 0.00
% 3.47/1.57  Index Deletion       : 0.00
% 3.47/1.57  Index Matching       : 0.00
% 3.47/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
