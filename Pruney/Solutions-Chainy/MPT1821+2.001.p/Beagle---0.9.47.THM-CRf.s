%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:09 EST 2020

% Result     : Theorem 5.43s
% Output     : CNFRefutation 5.76s
% Verified   : 
% Statistics : Number of formulae       :  237 (11104 expanded)
%              Number of leaves         :   32 (3999 expanded)
%              Depth                    :   23
%              Number of atoms          : 1052 (128363 expanded)
%              Number of equality atoms :   38 (4749 expanded)
%              Maximal formula depth    :   29 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > r3_tsep_1 > r1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_tsep_1,type,(
    k1_tsep_1: ( $i * $i * $i ) > $i )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r3_tsep_1,type,(
    r3_tsep_1: ( $i * $i * $i ) > $o )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_215,negated_conjecture,(
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
               => ( A = k1_tsep_1(A,B,C)
                 => ( r3_tsep_1(A,B,C)
                  <=> ( r1_tsep_1(B,C)
                      & ! [D] :
                          ( ( ~ v2_struct_0(D)
                            & v2_pre_topc(D)
                            & l1_pre_topc(D) )
                         => ! [E] :
                              ( ( v1_funct_1(E)
                                & v1_funct_2(E,u1_struct_0(A),u1_struct_0(D))
                                & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(D)))) )
                             => ( ( v1_funct_1(k2_tmap_1(A,D,E,B))
                                  & v1_funct_2(k2_tmap_1(A,D,E,B),u1_struct_0(B),u1_struct_0(D))
                                  & v5_pre_topc(k2_tmap_1(A,D,E,B),B,D)
                                  & m1_subset_1(k2_tmap_1(A,D,E,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(D))))
                                  & v1_funct_1(k2_tmap_1(A,D,E,C))
                                  & v1_funct_2(k2_tmap_1(A,D,E,C),u1_struct_0(C),u1_struct_0(D))
                                  & v5_pre_topc(k2_tmap_1(A,D,E,C),C,D)
                                  & m1_subset_1(k2_tmap_1(A,D,E,C),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(D)))) )
                               => ( v1_funct_1(E)
                                  & v1_funct_2(E,u1_struct_0(A),u1_struct_0(D))
                                  & v5_pre_topc(E,A,D)
                                  & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(D)))) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_tmap_1)).

tff(f_146,axiom,(
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
             => ( r3_tsep_1(A,B,C)
              <=> ( r1_tsep_1(B,C)
                  & ! [D] :
                      ( ( ~ v2_struct_0(D)
                        & v2_pre_topc(D)
                        & l1_pre_topc(D) )
                     => ! [E] :
                          ( ( v1_funct_1(E)
                            & v1_funct_2(E,u1_struct_0(k1_tsep_1(A,B,C)),u1_struct_0(D))
                            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,B,C)),u1_struct_0(D)))) )
                         => ( ( v1_funct_1(k3_tmap_1(A,D,k1_tsep_1(A,B,C),B,E))
                              & v1_funct_2(k3_tmap_1(A,D,k1_tsep_1(A,B,C),B,E),u1_struct_0(B),u1_struct_0(D))
                              & v5_pre_topc(k3_tmap_1(A,D,k1_tsep_1(A,B,C),B,E),B,D)
                              & m1_subset_1(k3_tmap_1(A,D,k1_tsep_1(A,B,C),B,E),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(D))))
                              & v1_funct_1(k3_tmap_1(A,D,k1_tsep_1(A,B,C),C,E))
                              & v1_funct_2(k3_tmap_1(A,D,k1_tsep_1(A,B,C),C,E),u1_struct_0(C),u1_struct_0(D))
                              & v5_pre_topc(k3_tmap_1(A,D,k1_tsep_1(A,B,C),C,E),C,D)
                              & m1_subset_1(k3_tmap_1(A,D,k1_tsep_1(A,B,C),C,E),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(D)))) )
                           => ( v1_funct_1(E)
                              & v1_funct_2(E,u1_struct_0(k1_tsep_1(A,B,C)),u1_struct_0(D))
                              & v5_pre_topc(E,k1_tsep_1(A,B,C),D)
                              & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,B,C)),u1_struct_0(D)))) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_tmap_1)).

tff(f_52,axiom,(
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

tff(f_150,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_84,axiom,(
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

tff(c_62,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_224,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | r1_tsep_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_260,plain,(
    r1_tsep_1('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_224])).

tff(c_88,plain,
    ( v1_funct_1('#skF_7')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_262,plain,
    ( v1_funct_1('#skF_7')
    | ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_88])).

tff(c_263,plain,(
    ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_262])).

tff(c_60,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_58,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_54,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_50,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_30,plain,(
    ! [A_47,B_75,C_89] :
      ( l1_pre_topc('#skF_1'(A_47,B_75,C_89))
      | r3_tsep_1(A_47,B_75,C_89)
      | ~ r1_tsep_1(B_75,C_89)
      | ~ m1_pre_topc(C_89,A_47)
      | v2_struct_0(C_89)
      | ~ m1_pre_topc(B_75,A_47)
      | v2_struct_0(B_75)
      | ~ l1_pre_topc(A_47)
      | ~ v2_pre_topc(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_28,plain,(
    ! [A_47,B_75,C_89] :
      ( v1_funct_1('#skF_2'(A_47,B_75,C_89))
      | r3_tsep_1(A_47,B_75,C_89)
      | ~ r1_tsep_1(B_75,C_89)
      | ~ m1_pre_topc(C_89,A_47)
      | v2_struct_0(C_89)
      | ~ m1_pre_topc(B_75,A_47)
      | v2_struct_0(B_75)
      | ~ l1_pre_topc(A_47)
      | ~ v2_pre_topc(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_32,plain,(
    ! [A_47,B_75,C_89] :
      ( v2_pre_topc('#skF_1'(A_47,B_75,C_89))
      | r3_tsep_1(A_47,B_75,C_89)
      | ~ r1_tsep_1(B_75,C_89)
      | ~ m1_pre_topc(C_89,A_47)
      | v2_struct_0(C_89)
      | ~ m1_pre_topc(B_75,A_47)
      | v2_struct_0(B_75)
      | ~ l1_pre_topc(A_47)
      | ~ v2_pre_topc(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_48,plain,(
    k1_tsep_1('#skF_3','#skF_4','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_299,plain,(
    ! [A_169,B_170,C_171] :
      ( v1_funct_2('#skF_2'(A_169,B_170,C_171),u1_struct_0(k1_tsep_1(A_169,B_170,C_171)),u1_struct_0('#skF_1'(A_169,B_170,C_171)))
      | r3_tsep_1(A_169,B_170,C_171)
      | ~ r1_tsep_1(B_170,C_171)
      | ~ m1_pre_topc(C_171,A_169)
      | v2_struct_0(C_171)
      | ~ m1_pre_topc(B_170,A_169)
      | v2_struct_0(B_170)
      | ~ l1_pre_topc(A_169)
      | ~ v2_pre_topc(A_169)
      | v2_struct_0(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_302,plain,
    ( v1_funct_2('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_299])).

tff(c_304,plain,
    ( v1_funct_2('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_50,c_260,c_302])).

tff(c_305,plain,(
    v1_funct_2('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_52,c_263,c_304])).

tff(c_322,plain,(
    ! [A_178,B_179,C_180] :
      ( m1_subset_1('#skF_2'(A_178,B_179,C_180),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_178,B_179,C_180)),u1_struct_0('#skF_1'(A_178,B_179,C_180)))))
      | r3_tsep_1(A_178,B_179,C_180)
      | ~ r1_tsep_1(B_179,C_180)
      | ~ m1_pre_topc(C_180,A_178)
      | v2_struct_0(C_180)
      | ~ m1_pre_topc(B_179,A_178)
      | v2_struct_0(B_179)
      | ~ l1_pre_topc(A_178)
      | ~ v2_pre_topc(A_178)
      | v2_struct_0(A_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_325,plain,
    ( m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_322])).

tff(c_327,plain,
    ( m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_50,c_260,c_325])).

tff(c_328,plain,(
    m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))))) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_52,c_263,c_327])).

tff(c_343,plain,(
    ! [A_187,B_188,C_189,D_190] :
      ( k2_partfun1(u1_struct_0(A_187),u1_struct_0(B_188),C_189,u1_struct_0(D_190)) = k2_tmap_1(A_187,B_188,C_189,D_190)
      | ~ m1_pre_topc(D_190,A_187)
      | ~ m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_187),u1_struct_0(B_188))))
      | ~ v1_funct_2(C_189,u1_struct_0(A_187),u1_struct_0(B_188))
      | ~ v1_funct_1(C_189)
      | ~ l1_pre_topc(B_188)
      | ~ v2_pre_topc(B_188)
      | v2_struct_0(B_188)
      | ~ l1_pre_topc(A_187)
      | ~ v2_pre_topc(A_187)
      | v2_struct_0(A_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_345,plain,(
    ! [D_190] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')),'#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(D_190)) = k2_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_2'('#skF_3','#skF_4','#skF_5'),D_190)
      | ~ m1_pre_topc(D_190,'#skF_3')
      | ~ v1_funct_2('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
      | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5'))
      | ~ l1_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
      | ~ v2_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
      | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_328,c_343])).

tff(c_350,plain,(
    ! [D_190] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')),'#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(D_190)) = k2_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_2'('#skF_3','#skF_4','#skF_5'),D_190)
      | ~ m1_pre_topc(D_190,'#skF_3')
      | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5'))
      | ~ l1_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
      | ~ v2_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
      | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_305,c_345])).

tff(c_351,plain,(
    ! [D_190] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')),'#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(D_190)) = k2_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_2'('#skF_3','#skF_4','#skF_5'),D_190)
      | ~ m1_pre_topc(D_190,'#skF_3')
      | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5'))
      | ~ l1_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
      | ~ v2_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
      | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_350])).

tff(c_426,plain,(
    ~ v2_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_351])).

tff(c_429,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_426])).

tff(c_432,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_50,c_260,c_429])).

tff(c_434,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_52,c_263,c_432])).

tff(c_435,plain,(
    ! [D_190] :
      ( ~ l1_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
      | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5'))
      | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
      | k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')),'#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(D_190)) = k2_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_2'('#skF_3','#skF_4','#skF_5'),D_190)
      | ~ m1_pre_topc(D_190,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_351])).

tff(c_439,plain,(
    ~ v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_435])).

tff(c_442,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_439])).

tff(c_445,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_50,c_260,c_442])).

tff(c_447,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_52,c_263,c_445])).

tff(c_448,plain,(
    ! [D_190] :
      ( ~ l1_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
      | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
      | k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')),'#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(D_190)) = k2_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_2'('#skF_3','#skF_4','#skF_5'),D_190)
      | ~ m1_pre_topc(D_190,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_435])).

tff(c_450,plain,(
    ~ l1_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_448])).

tff(c_464,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_450])).

tff(c_467,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_50,c_260,c_464])).

tff(c_469,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_52,c_263,c_467])).

tff(c_470,plain,(
    ! [D_190] :
      ( v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
      | k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')),'#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(D_190)) = k2_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_2'('#skF_3','#skF_4','#skF_5'),D_190)
      | ~ m1_pre_topc(D_190,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_448])).

tff(c_472,plain,(
    v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_470])).

tff(c_34,plain,(
    ! [A_47,B_75,C_89] :
      ( ~ v2_struct_0('#skF_1'(A_47,B_75,C_89))
      | r3_tsep_1(A_47,B_75,C_89)
      | ~ r1_tsep_1(B_75,C_89)
      | ~ m1_pre_topc(C_89,A_47)
      | v2_struct_0(C_89)
      | ~ m1_pre_topc(B_75,A_47)
      | v2_struct_0(B_75)
      | ~ l1_pre_topc(A_47)
      | ~ v2_pre_topc(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_477,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_472,c_34])).

tff(c_480,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_50,c_260,c_477])).

tff(c_482,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_52,c_263,c_480])).

tff(c_484,plain,(
    ~ v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_470])).

tff(c_449,plain,(
    v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_435])).

tff(c_581,plain,(
    ! [A_216,B_217,C_218] :
      ( ~ m1_subset_1('#skF_2'(A_216,B_217,C_218),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_216,B_217,C_218)),u1_struct_0('#skF_1'(A_216,B_217,C_218)))))
      | ~ v5_pre_topc('#skF_2'(A_216,B_217,C_218),k1_tsep_1(A_216,B_217,C_218),'#skF_1'(A_216,B_217,C_218))
      | ~ v1_funct_2('#skF_2'(A_216,B_217,C_218),u1_struct_0(k1_tsep_1(A_216,B_217,C_218)),u1_struct_0('#skF_1'(A_216,B_217,C_218)))
      | ~ v1_funct_1('#skF_2'(A_216,B_217,C_218))
      | r3_tsep_1(A_216,B_217,C_218)
      | ~ r1_tsep_1(B_217,C_218)
      | ~ m1_pre_topc(C_218,A_216)
      | v2_struct_0(C_218)
      | ~ m1_pre_topc(B_217,A_216)
      | v2_struct_0(B_217)
      | ~ l1_pre_topc(A_216)
      | ~ v2_pre_topc(A_216)
      | v2_struct_0(A_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_587,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v5_pre_topc('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_581])).

tff(c_590,plain,
    ( ~ v5_pre_topc('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_50,c_260,c_449,c_305,c_48,c_48,c_328,c_587])).

tff(c_591,plain,(
    ~ v5_pre_topc('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_52,c_263,c_590])).

tff(c_436,plain,(
    v2_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_351])).

tff(c_471,plain,(
    l1_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_448])).

tff(c_46,plain,(
    ! [A_100] :
      ( m1_pre_topc(A_100,A_100)
      | ~ l1_pre_topc(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_395,plain,(
    ! [A_207,D_205,C_206,B_203,E_204] :
      ( k3_tmap_1(A_207,B_203,C_206,D_205,E_204) = k2_partfun1(u1_struct_0(C_206),u1_struct_0(B_203),E_204,u1_struct_0(D_205))
      | ~ m1_pre_topc(D_205,C_206)
      | ~ m1_subset_1(E_204,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_206),u1_struct_0(B_203))))
      | ~ v1_funct_2(E_204,u1_struct_0(C_206),u1_struct_0(B_203))
      | ~ v1_funct_1(E_204)
      | ~ m1_pre_topc(D_205,A_207)
      | ~ m1_pre_topc(C_206,A_207)
      | ~ l1_pre_topc(B_203)
      | ~ v2_pre_topc(B_203)
      | v2_struct_0(B_203)
      | ~ l1_pre_topc(A_207)
      | ~ v2_pre_topc(A_207)
      | v2_struct_0(A_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_403,plain,(
    ! [A_207,D_205] :
      ( k3_tmap_1(A_207,'#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3',D_205,'#skF_2'('#skF_3','#skF_4','#skF_5')) = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')),'#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(D_205))
      | ~ m1_pre_topc(D_205,'#skF_3')
      | ~ v1_funct_2('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
      | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5'))
      | ~ m1_pre_topc(D_205,A_207)
      | ~ m1_pre_topc('#skF_3',A_207)
      | ~ l1_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
      | ~ v2_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
      | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
      | ~ l1_pre_topc(A_207)
      | ~ v2_pre_topc(A_207)
      | v2_struct_0(A_207) ) ),
    inference(resolution,[status(thm)],[c_328,c_395])).

tff(c_413,plain,(
    ! [A_207,D_205] :
      ( k3_tmap_1(A_207,'#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3',D_205,'#skF_2'('#skF_3','#skF_4','#skF_5')) = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')),'#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(D_205))
      | ~ m1_pre_topc(D_205,'#skF_3')
      | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5'))
      | ~ m1_pre_topc(D_205,A_207)
      | ~ m1_pre_topc('#skF_3',A_207)
      | ~ l1_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
      | ~ v2_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
      | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
      | ~ l1_pre_topc(A_207)
      | ~ v2_pre_topc(A_207)
      | v2_struct_0(A_207) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_305,c_403])).

tff(c_495,plain,(
    ! [A_207,D_205] :
      ( k3_tmap_1(A_207,'#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3',D_205,'#skF_2'('#skF_3','#skF_4','#skF_5')) = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')),'#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(D_205))
      | ~ m1_pre_topc(D_205,'#skF_3')
      | ~ m1_pre_topc(D_205,A_207)
      | ~ m1_pre_topc('#skF_3',A_207)
      | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
      | ~ l1_pre_topc(A_207)
      | ~ v2_pre_topc(A_207)
      | v2_struct_0(A_207) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_436,c_471,c_449,c_413])).

tff(c_497,plain,(
    ! [A_212,D_213] :
      ( k3_tmap_1(A_212,'#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3',D_213,'#skF_2'('#skF_3','#skF_4','#skF_5')) = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')),'#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(D_213))
      | ~ m1_pre_topc(D_213,'#skF_3')
      | ~ m1_pre_topc(D_213,A_212)
      | ~ m1_pre_topc('#skF_3',A_212)
      | ~ l1_pre_topc(A_212)
      | ~ v2_pre_topc(A_212)
      | v2_struct_0(A_212) ) ),
    inference(negUnitSimplification,[status(thm)],[c_484,c_495])).

tff(c_483,plain,(
    ! [D_190] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')),'#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(D_190)) = k2_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_2'('#skF_3','#skF_4','#skF_5'),D_190)
      | ~ m1_pre_topc(D_190,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_470])).

tff(c_518,plain,(
    ! [A_214,D_215] :
      ( k3_tmap_1(A_214,'#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3',D_215,'#skF_2'('#skF_3','#skF_4','#skF_5')) = k2_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_2'('#skF_3','#skF_4','#skF_5'),D_215)
      | ~ m1_pre_topc(D_215,'#skF_3')
      | ~ m1_pre_topc(D_215,'#skF_3')
      | ~ m1_pre_topc(D_215,A_214)
      | ~ m1_pre_topc('#skF_3',A_214)
      | ~ l1_pre_topc(A_214)
      | ~ v2_pre_topc(A_214)
      | v2_struct_0(A_214) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_497,c_483])).

tff(c_313,plain,(
    ! [A_175,B_176,C_177] :
      ( v1_funct_1(k3_tmap_1(A_175,'#skF_1'(A_175,B_176,C_177),k1_tsep_1(A_175,B_176,C_177),C_177,'#skF_2'(A_175,B_176,C_177)))
      | r3_tsep_1(A_175,B_176,C_177)
      | ~ r1_tsep_1(B_176,C_177)
      | ~ m1_pre_topc(C_177,A_175)
      | v2_struct_0(C_177)
      | ~ m1_pre_topc(B_176,A_175)
      | v2_struct_0(B_176)
      | ~ l1_pre_topc(A_175)
      | ~ v2_pre_topc(A_175)
      | v2_struct_0(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_316,plain,
    ( v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3','#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_313])).

tff(c_318,plain,
    ( v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3','#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_50,c_260,c_316])).

tff(c_319,plain,(
    v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3','#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_52,c_263,c_318])).

tff(c_545,plain,
    ( v1_funct_1(k2_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_5'))
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_518,c_319])).

tff(c_575,plain,
    ( v1_funct_1(k2_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_5'))
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_50,c_50,c_50,c_545])).

tff(c_576,plain,
    ( v1_funct_1(k2_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_5'))
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_575])).

tff(c_592,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_576])).

tff(c_595,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_592])).

tff(c_599,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_595])).

tff(c_601,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_576])).

tff(c_306,plain,(
    ! [A_172,B_173,C_174] :
      ( v1_funct_1(k3_tmap_1(A_172,'#skF_1'(A_172,B_173,C_174),k1_tsep_1(A_172,B_173,C_174),B_173,'#skF_2'(A_172,B_173,C_174)))
      | r3_tsep_1(A_172,B_173,C_174)
      | ~ r1_tsep_1(B_173,C_174)
      | ~ m1_pre_topc(C_174,A_172)
      | v2_struct_0(C_174)
      | ~ m1_pre_topc(B_173,A_172)
      | v2_struct_0(B_173)
      | ~ l1_pre_topc(A_172)
      | ~ v2_pre_topc(A_172)
      | v2_struct_0(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_309,plain,
    ( v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_306])).

tff(c_311,plain,
    ( v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_50,c_260,c_309])).

tff(c_312,plain,(
    v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_52,c_263,c_311])).

tff(c_548,plain,
    ( v1_funct_1(k2_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_518,c_312])).

tff(c_578,plain,
    ( v1_funct_1(k2_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_54,c_54,c_548])).

tff(c_579,plain,
    ( v1_funct_1(k2_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_578])).

tff(c_605,plain,(
    v1_funct_1(k2_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_601,c_579])).

tff(c_353,plain,(
    ! [A_191,B_192,C_193] :
      ( v1_funct_2(k3_tmap_1(A_191,'#skF_1'(A_191,B_192,C_193),k1_tsep_1(A_191,B_192,C_193),B_192,'#skF_2'(A_191,B_192,C_193)),u1_struct_0(B_192),u1_struct_0('#skF_1'(A_191,B_192,C_193)))
      | r3_tsep_1(A_191,B_192,C_193)
      | ~ r1_tsep_1(B_192,C_193)
      | ~ m1_pre_topc(C_193,A_191)
      | v2_struct_0(C_193)
      | ~ m1_pre_topc(B_192,A_191)
      | v2_struct_0(B_192)
      | ~ l1_pre_topc(A_191)
      | ~ v2_pre_topc(A_191)
      | v2_struct_0(A_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_356,plain,
    ( v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_353])).

tff(c_358,plain,
    ( v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_50,c_260,c_356])).

tff(c_359,plain,(
    v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_52,c_263,c_358])).

tff(c_536,plain,
    ( v1_funct_2(k2_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_518,c_359])).

tff(c_566,plain,
    ( v1_funct_2(k2_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_54,c_54,c_536])).

tff(c_567,plain,
    ( v1_funct_2(k2_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_566])).

tff(c_615,plain,(
    v1_funct_2(k2_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_601,c_567])).

tff(c_329,plain,(
    ! [A_181,B_182,C_183] :
      ( v5_pre_topc(k3_tmap_1(A_181,'#skF_1'(A_181,B_182,C_183),k1_tsep_1(A_181,B_182,C_183),B_182,'#skF_2'(A_181,B_182,C_183)),B_182,'#skF_1'(A_181,B_182,C_183))
      | r3_tsep_1(A_181,B_182,C_183)
      | ~ r1_tsep_1(B_182,C_183)
      | ~ m1_pre_topc(C_183,A_181)
      | v2_struct_0(C_183)
      | ~ m1_pre_topc(B_182,A_181)
      | v2_struct_0(B_182)
      | ~ l1_pre_topc(A_181)
      | ~ v2_pre_topc(A_181)
      | v2_struct_0(A_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_332,plain,
    ( v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_329])).

tff(c_334,plain,
    ( v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_50,c_260,c_332])).

tff(c_335,plain,(
    v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_52,c_263,c_334])).

tff(c_542,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4'),'#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_518,c_335])).

tff(c_572,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4'),'#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_54,c_54,c_542])).

tff(c_573,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4'),'#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_572])).

tff(c_609,plain,(
    v5_pre_topc(k2_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4'),'#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_601,c_573])).

tff(c_600,plain,(
    v1_funct_1(k2_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_5')) ),
    inference(splitRight,[status(thm)],[c_576])).

tff(c_362,plain,(
    ! [A_194,B_195,C_196] :
      ( v1_funct_2(k3_tmap_1(A_194,'#skF_1'(A_194,B_195,C_196),k1_tsep_1(A_194,B_195,C_196),C_196,'#skF_2'(A_194,B_195,C_196)),u1_struct_0(C_196),u1_struct_0('#skF_1'(A_194,B_195,C_196)))
      | r3_tsep_1(A_194,B_195,C_196)
      | ~ r1_tsep_1(B_195,C_196)
      | ~ m1_pre_topc(C_196,A_194)
      | v2_struct_0(C_196)
      | ~ m1_pre_topc(B_195,A_194)
      | v2_struct_0(B_195)
      | ~ l1_pre_topc(A_194)
      | ~ v2_pre_topc(A_194)
      | v2_struct_0(A_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_365,plain,
    ( v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3','#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_362])).

tff(c_367,plain,
    ( v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3','#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_50,c_260,c_365])).

tff(c_368,plain,(
    v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3','#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_52,c_263,c_367])).

tff(c_533,plain,
    ( v1_funct_2(k2_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_518,c_368])).

tff(c_563,plain,
    ( v1_funct_2(k2_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_50,c_50,c_50,c_533])).

tff(c_564,plain,
    ( v1_funct_2(k2_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_563])).

tff(c_613,plain,(
    v1_funct_2(k2_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_601,c_564])).

tff(c_336,plain,(
    ! [A_184,B_185,C_186] :
      ( v5_pre_topc(k3_tmap_1(A_184,'#skF_1'(A_184,B_185,C_186),k1_tsep_1(A_184,B_185,C_186),C_186,'#skF_2'(A_184,B_185,C_186)),C_186,'#skF_1'(A_184,B_185,C_186))
      | r3_tsep_1(A_184,B_185,C_186)
      | ~ r1_tsep_1(B_185,C_186)
      | ~ m1_pre_topc(C_186,A_184)
      | v2_struct_0(C_186)
      | ~ m1_pre_topc(B_185,A_184)
      | v2_struct_0(B_185)
      | ~ l1_pre_topc(A_184)
      | ~ v2_pre_topc(A_184)
      | v2_struct_0(A_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_339,plain,
    ( v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3','#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_5','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_336])).

tff(c_341,plain,
    ( v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3','#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_5','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_50,c_260,c_339])).

tff(c_342,plain,(
    v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3','#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_5','#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_52,c_263,c_341])).

tff(c_539,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_5'),'#skF_5','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_518,c_342])).

tff(c_569,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_5'),'#skF_5','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_50,c_50,c_50,c_539])).

tff(c_570,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_5'),'#skF_5','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_569])).

tff(c_607,plain,(
    v5_pre_topc(k2_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_5'),'#skF_5','#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_601,c_570])).

tff(c_385,plain,(
    ! [A_200,B_201,C_202] :
      ( m1_subset_1(k3_tmap_1(A_200,'#skF_1'(A_200,B_201,C_202),k1_tsep_1(A_200,B_201,C_202),C_202,'#skF_2'(A_200,B_201,C_202)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_202),u1_struct_0('#skF_1'(A_200,B_201,C_202)))))
      | r3_tsep_1(A_200,B_201,C_202)
      | ~ r1_tsep_1(B_201,C_202)
      | ~ m1_pre_topc(C_202,A_200)
      | v2_struct_0(C_202)
      | ~ m1_pre_topc(B_201,A_200)
      | v2_struct_0(B_201)
      | ~ l1_pre_topc(A_200)
      | ~ v2_pre_topc(A_200)
      | v2_struct_0(A_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_390,plain,
    ( m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3','#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_385])).

tff(c_393,plain,
    ( m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3','#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_50,c_260,c_390])).

tff(c_394,plain,(
    m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3','#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))))) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_52,c_263,c_393])).

tff(c_527,plain,
    ( m1_subset_1(k2_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_518,c_394])).

tff(c_557,plain,
    ( m1_subset_1(k2_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_50,c_50,c_50,c_527])).

tff(c_558,plain,
    ( m1_subset_1(k2_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_557])).

tff(c_617,plain,(
    m1_subset_1(k2_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_601,c_558])).

tff(c_128,plain,(
    ! [E_150,D_148] :
      ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
      | v5_pre_topc(E_150,'#skF_3',D_148)
      | ~ m1_subset_1(k2_tmap_1('#skF_3',D_148,E_150,'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(D_148))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_3',D_148,E_150,'#skF_5'),'#skF_5',D_148)
      | ~ v1_funct_2(k2_tmap_1('#skF_3',D_148,E_150,'#skF_5'),u1_struct_0('#skF_5'),u1_struct_0(D_148))
      | ~ v1_funct_1(k2_tmap_1('#skF_3',D_148,E_150,'#skF_5'))
      | ~ m1_subset_1(k2_tmap_1('#skF_3',D_148,E_150,'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(D_148))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_3',D_148,E_150,'#skF_4'),'#skF_4',D_148)
      | ~ v1_funct_2(k2_tmap_1('#skF_3',D_148,E_150,'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0(D_148))
      | ~ v1_funct_1(k2_tmap_1('#skF_3',D_148,E_150,'#skF_4'))
      | ~ m1_subset_1(E_150,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(D_148))))
      | ~ v1_funct_2(E_150,u1_struct_0('#skF_3'),u1_struct_0(D_148))
      | ~ v1_funct_1(E_150)
      | ~ l1_pre_topc(D_148)
      | ~ v2_pre_topc(D_148)
      | v2_struct_0(D_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_294,plain,(
    ! [E_150,D_148] :
      ( v5_pre_topc(E_150,'#skF_3',D_148)
      | ~ m1_subset_1(k2_tmap_1('#skF_3',D_148,E_150,'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(D_148))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_3',D_148,E_150,'#skF_5'),'#skF_5',D_148)
      | ~ v1_funct_2(k2_tmap_1('#skF_3',D_148,E_150,'#skF_5'),u1_struct_0('#skF_5'),u1_struct_0(D_148))
      | ~ v1_funct_1(k2_tmap_1('#skF_3',D_148,E_150,'#skF_5'))
      | ~ m1_subset_1(k2_tmap_1('#skF_3',D_148,E_150,'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(D_148))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_3',D_148,E_150,'#skF_4'),'#skF_4',D_148)
      | ~ v1_funct_2(k2_tmap_1('#skF_3',D_148,E_150,'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0(D_148))
      | ~ v1_funct_1(k2_tmap_1('#skF_3',D_148,E_150,'#skF_4'))
      | ~ m1_subset_1(E_150,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(D_148))))
      | ~ v1_funct_2(E_150,u1_struct_0('#skF_3'),u1_struct_0(D_148))
      | ~ v1_funct_1(E_150)
      | ~ l1_pre_topc(D_148)
      | ~ v2_pre_topc(D_148)
      | v2_struct_0(D_148) ) ),
    inference(negUnitSimplification,[status(thm)],[c_263,c_128])).

tff(c_624,plain,
    ( v5_pre_topc('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v5_pre_topc(k2_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_5'),'#skF_5','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1(k2_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_5'))
    | ~ m1_subset_1(k2_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4'),'#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1(k2_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4'))
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v1_funct_2('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v2_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_617,c_294])).

tff(c_635,plain,
    ( v5_pre_topc('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1(k2_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_436,c_471,c_449,c_305,c_328,c_605,c_615,c_609,c_600,c_613,c_607,c_624])).

tff(c_636,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))))) ),
    inference(negUnitSimplification,[status(thm)],[c_484,c_591,c_635])).

tff(c_369,plain,(
    ! [A_197,B_198,C_199] :
      ( m1_subset_1(k3_tmap_1(A_197,'#skF_1'(A_197,B_198,C_199),k1_tsep_1(A_197,B_198,C_199),B_198,'#skF_2'(A_197,B_198,C_199)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_198),u1_struct_0('#skF_1'(A_197,B_198,C_199)))))
      | r3_tsep_1(A_197,B_198,C_199)
      | ~ r1_tsep_1(B_198,C_199)
      | ~ m1_pre_topc(C_199,A_197)
      | v2_struct_0(C_199)
      | ~ m1_pre_topc(B_198,A_197)
      | v2_struct_0(B_198)
      | ~ l1_pre_topc(A_197)
      | ~ v2_pre_topc(A_197)
      | v2_struct_0(A_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_374,plain,
    ( m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_369])).

tff(c_377,plain,
    ( m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_50,c_260,c_374])).

tff(c_378,plain,(
    m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))))) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_52,c_263,c_377])).

tff(c_530,plain,
    ( m1_subset_1(k2_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_518,c_378])).

tff(c_560,plain,
    ( m1_subset_1(k2_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_54,c_54,c_530])).

tff(c_561,plain,
    ( m1_subset_1(k2_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_560])).

tff(c_640,plain,(
    m1_subset_1(k2_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_601,c_561])).

tff(c_641,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_636,c_640])).

tff(c_643,plain,(
    r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_262])).

tff(c_94,plain,
    ( ~ v2_struct_0('#skF_6')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_647,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_643,c_260,c_94])).

tff(c_642,plain,(
    v1_funct_1('#skF_7') ),
    inference(splitRight,[status(thm)],[c_262])).

tff(c_86,plain,
    ( v1_funct_2('#skF_7',u1_struct_0('#skF_3'),u1_struct_0('#skF_6'))
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_655,plain,(
    v1_funct_2('#skF_7',u1_struct_0('#skF_3'),u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_643,c_260,c_86])).

tff(c_84,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_6'))))
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_659,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_6')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_643,c_260,c_84])).

tff(c_66,plain,
    ( ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_6'))))
    | ~ v5_pre_topc('#skF_7','#skF_3','#skF_6')
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_3'),u1_struct_0('#skF_6'))
    | ~ v1_funct_1('#skF_7')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_679,plain,(
    ~ v5_pre_topc('#skF_7','#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_643,c_260,c_642,c_655,c_659,c_66])).

tff(c_92,plain,
    ( v2_pre_topc('#skF_6')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_649,plain,(
    v2_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_643,c_260,c_92])).

tff(c_90,plain,
    ( l1_pre_topc('#skF_6')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_645,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_643,c_260,c_90])).

tff(c_82,plain,
    ( v1_funct_1(k2_tmap_1('#skF_3','#skF_6','#skF_7','#skF_4'))
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_653,plain,(
    v1_funct_1(k2_tmap_1('#skF_3','#skF_6','#skF_7','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_643,c_260,c_82])).

tff(c_798,plain,(
    ! [E_270,B_269,D_271,A_273,C_272] :
      ( k3_tmap_1(A_273,B_269,C_272,D_271,E_270) = k2_partfun1(u1_struct_0(C_272),u1_struct_0(B_269),E_270,u1_struct_0(D_271))
      | ~ m1_pre_topc(D_271,C_272)
      | ~ m1_subset_1(E_270,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_272),u1_struct_0(B_269))))
      | ~ v1_funct_2(E_270,u1_struct_0(C_272),u1_struct_0(B_269))
      | ~ v1_funct_1(E_270)
      | ~ m1_pre_topc(D_271,A_273)
      | ~ m1_pre_topc(C_272,A_273)
      | ~ l1_pre_topc(B_269)
      | ~ v2_pre_topc(B_269)
      | v2_struct_0(B_269)
      | ~ l1_pre_topc(A_273)
      | ~ v2_pre_topc(A_273)
      | v2_struct_0(A_273) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_810,plain,(
    ! [A_273,D_271] :
      ( k3_tmap_1(A_273,'#skF_6','#skF_3',D_271,'#skF_7') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_6'),'#skF_7',u1_struct_0(D_271))
      | ~ m1_pre_topc(D_271,'#skF_3')
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_3'),u1_struct_0('#skF_6'))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_pre_topc(D_271,A_273)
      | ~ m1_pre_topc('#skF_3',A_273)
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_pre_topc(A_273)
      | ~ v2_pre_topc(A_273)
      | v2_struct_0(A_273) ) ),
    inference(resolution,[status(thm)],[c_659,c_798])).

tff(c_824,plain,(
    ! [A_273,D_271] :
      ( k3_tmap_1(A_273,'#skF_6','#skF_3',D_271,'#skF_7') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_6'),'#skF_7',u1_struct_0(D_271))
      | ~ m1_pre_topc(D_271,'#skF_3')
      | ~ m1_pre_topc(D_271,A_273)
      | ~ m1_pre_topc('#skF_3',A_273)
      | v2_struct_0('#skF_6')
      | ~ l1_pre_topc(A_273)
      | ~ v2_pre_topc(A_273)
      | v2_struct_0(A_273) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_649,c_645,c_642,c_655,c_810])).

tff(c_826,plain,(
    ! [A_274,D_275] :
      ( k3_tmap_1(A_274,'#skF_6','#skF_3',D_275,'#skF_7') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_6'),'#skF_7',u1_struct_0(D_275))
      | ~ m1_pre_topc(D_275,'#skF_3')
      | ~ m1_pre_topc(D_275,A_274)
      | ~ m1_pre_topc('#skF_3',A_274)
      | ~ l1_pre_topc(A_274)
      | ~ v2_pre_topc(A_274)
      | v2_struct_0(A_274) ) ),
    inference(negUnitSimplification,[status(thm)],[c_647,c_824])).

tff(c_830,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_6'),'#skF_7',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_3','#skF_6','#skF_3','#skF_5','#skF_7')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_826])).

tff(c_836,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_6'),'#skF_7',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_3','#skF_6','#skF_3','#skF_5','#skF_7')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_50,c_830])).

tff(c_837,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_6'),'#skF_7',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_3','#skF_6','#skF_3','#skF_5','#skF_7')
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_836])).

tff(c_842,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_837])).

tff(c_856,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_842])).

tff(c_860,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_856])).

tff(c_862,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_837])).

tff(c_832,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_6'),'#skF_7',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_3','#skF_6','#skF_3','#skF_4','#skF_7')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_826])).

tff(c_840,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_6'),'#skF_7',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_3','#skF_6','#skF_3','#skF_4','#skF_7')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_832])).

tff(c_841,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_6'),'#skF_7',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_3','#skF_6','#skF_3','#skF_4','#skF_7')
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_840])).

tff(c_955,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_6'),'#skF_7',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_3','#skF_6','#skF_3','#skF_4','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_862,c_841])).

tff(c_729,plain,(
    ! [A_252,B_253,C_254,D_255] :
      ( k2_partfun1(u1_struct_0(A_252),u1_struct_0(B_253),C_254,u1_struct_0(D_255)) = k2_tmap_1(A_252,B_253,C_254,D_255)
      | ~ m1_pre_topc(D_255,A_252)
      | ~ m1_subset_1(C_254,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_252),u1_struct_0(B_253))))
      | ~ v1_funct_2(C_254,u1_struct_0(A_252),u1_struct_0(B_253))
      | ~ v1_funct_1(C_254)
      | ~ l1_pre_topc(B_253)
      | ~ v2_pre_topc(B_253)
      | v2_struct_0(B_253)
      | ~ l1_pre_topc(A_252)
      | ~ v2_pre_topc(A_252)
      | v2_struct_0(A_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_737,plain,(
    ! [D_255] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_6'),'#skF_7',u1_struct_0(D_255)) = k2_tmap_1('#skF_3','#skF_6','#skF_7',D_255)
      | ~ m1_pre_topc(D_255,'#skF_3')
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_3'),u1_struct_0('#skF_6'))
      | ~ v1_funct_1('#skF_7')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_659,c_729])).

tff(c_749,plain,(
    ! [D_255] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_6'),'#skF_7',u1_struct_0(D_255)) = k2_tmap_1('#skF_3','#skF_6','#skF_7',D_255)
      | ~ m1_pre_topc(D_255,'#skF_3')
      | v2_struct_0('#skF_6')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_649,c_645,c_642,c_655,c_737])).

tff(c_750,plain,(
    ! [D_255] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_6'),'#skF_7',u1_struct_0(D_255)) = k2_tmap_1('#skF_3','#skF_6','#skF_7',D_255)
      | ~ m1_pre_topc(D_255,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_647,c_749])).

tff(c_959,plain,
    ( k3_tmap_1('#skF_3','#skF_6','#skF_3','#skF_4','#skF_7') = k2_tmap_1('#skF_3','#skF_6','#skF_7','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_955,c_750])).

tff(c_966,plain,(
    k3_tmap_1('#skF_3','#skF_6','#skF_3','#skF_4','#skF_7') = k2_tmap_1('#skF_3','#skF_6','#skF_7','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_959])).

tff(c_80,plain,
    ( v1_funct_2(k2_tmap_1('#skF_3','#skF_6','#skF_7','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_6'))
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_663,plain,(
    v1_funct_2(k2_tmap_1('#skF_3','#skF_6','#skF_7','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_643,c_260,c_80])).

tff(c_78,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_3','#skF_6','#skF_7','#skF_4'),'#skF_4','#skF_6')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_661,plain,(
    v5_pre_topc(k2_tmap_1('#skF_3','#skF_6','#skF_7','#skF_4'),'#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_643,c_260,c_78])).

tff(c_76,plain,
    ( m1_subset_1(k2_tmap_1('#skF_3','#skF_6','#skF_7','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_6'))))
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_667,plain,(
    m1_subset_1(k2_tmap_1('#skF_3','#skF_6','#skF_7','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_6')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_643,c_260,c_76])).

tff(c_74,plain,
    ( v1_funct_1(k2_tmap_1('#skF_3','#skF_6','#skF_7','#skF_5'))
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_651,plain,(
    v1_funct_1(k2_tmap_1('#skF_3','#skF_6','#skF_7','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_643,c_260,c_74])).

tff(c_861,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_6'),'#skF_7',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_3','#skF_6','#skF_3','#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_837])).

tff(c_872,plain,
    ( k3_tmap_1('#skF_3','#skF_6','#skF_3','#skF_5','#skF_7') = k2_tmap_1('#skF_3','#skF_6','#skF_7','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_861,c_750])).

tff(c_879,plain,(
    k3_tmap_1('#skF_3','#skF_6','#skF_3','#skF_5','#skF_7') = k2_tmap_1('#skF_3','#skF_6','#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_872])).

tff(c_72,plain,
    ( v1_funct_2(k2_tmap_1('#skF_3','#skF_6','#skF_7','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_6'))
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_665,plain,(
    v1_funct_2(k2_tmap_1('#skF_3','#skF_6','#skF_7','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_643,c_260,c_72])).

tff(c_70,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_3','#skF_6','#skF_7','#skF_5'),'#skF_5','#skF_6')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_657,plain,(
    v5_pre_topc(k2_tmap_1('#skF_3','#skF_6','#skF_7','#skF_5'),'#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_643,c_260,c_70])).

tff(c_68,plain,
    ( m1_subset_1(k2_tmap_1('#skF_3','#skF_6','#skF_7','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_6'))))
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_669,plain,(
    m1_subset_1(k2_tmap_1('#skF_3','#skF_6','#skF_7','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_6')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_643,c_260,c_68])).

tff(c_1333,plain,(
    ! [A_315,D_317,E_319,C_316,B_318] :
      ( v5_pre_topc(E_319,k1_tsep_1(A_315,B_318,C_316),D_317)
      | ~ m1_subset_1(k3_tmap_1(A_315,D_317,k1_tsep_1(A_315,B_318,C_316),C_316,E_319),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_316),u1_struct_0(D_317))))
      | ~ v5_pre_topc(k3_tmap_1(A_315,D_317,k1_tsep_1(A_315,B_318,C_316),C_316,E_319),C_316,D_317)
      | ~ v1_funct_2(k3_tmap_1(A_315,D_317,k1_tsep_1(A_315,B_318,C_316),C_316,E_319),u1_struct_0(C_316),u1_struct_0(D_317))
      | ~ v1_funct_1(k3_tmap_1(A_315,D_317,k1_tsep_1(A_315,B_318,C_316),C_316,E_319))
      | ~ m1_subset_1(k3_tmap_1(A_315,D_317,k1_tsep_1(A_315,B_318,C_316),B_318,E_319),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_318),u1_struct_0(D_317))))
      | ~ v5_pre_topc(k3_tmap_1(A_315,D_317,k1_tsep_1(A_315,B_318,C_316),B_318,E_319),B_318,D_317)
      | ~ v1_funct_2(k3_tmap_1(A_315,D_317,k1_tsep_1(A_315,B_318,C_316),B_318,E_319),u1_struct_0(B_318),u1_struct_0(D_317))
      | ~ v1_funct_1(k3_tmap_1(A_315,D_317,k1_tsep_1(A_315,B_318,C_316),B_318,E_319))
      | ~ m1_subset_1(E_319,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_315,B_318,C_316)),u1_struct_0(D_317))))
      | ~ v1_funct_2(E_319,u1_struct_0(k1_tsep_1(A_315,B_318,C_316)),u1_struct_0(D_317))
      | ~ v1_funct_1(E_319)
      | ~ l1_pre_topc(D_317)
      | ~ v2_pre_topc(D_317)
      | v2_struct_0(D_317)
      | ~ r3_tsep_1(A_315,B_318,C_316)
      | ~ m1_pre_topc(C_316,A_315)
      | v2_struct_0(C_316)
      | ~ m1_pre_topc(B_318,A_315)
      | v2_struct_0(B_318)
      | ~ l1_pre_topc(A_315)
      | ~ v2_pre_topc(A_315)
      | v2_struct_0(A_315) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_1343,plain,(
    ! [E_319,D_317] :
      ( v5_pre_topc(E_319,k1_tsep_1('#skF_3','#skF_4','#skF_5'),D_317)
      | ~ m1_subset_1(k3_tmap_1('#skF_3',D_317,'#skF_3','#skF_5',E_319),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(D_317))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_3',D_317,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_319),'#skF_5',D_317)
      | ~ v1_funct_2(k3_tmap_1('#skF_3',D_317,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_319),u1_struct_0('#skF_5'),u1_struct_0(D_317))
      | ~ v1_funct_1(k3_tmap_1('#skF_3',D_317,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_319))
      | ~ m1_subset_1(k3_tmap_1('#skF_3',D_317,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_319),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(D_317))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_3',D_317,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_319),'#skF_4',D_317)
      | ~ v1_funct_2(k3_tmap_1('#skF_3',D_317,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_319),u1_struct_0('#skF_4'),u1_struct_0(D_317))
      | ~ v1_funct_1(k3_tmap_1('#skF_3',D_317,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_319))
      | ~ m1_subset_1(E_319,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0(D_317))))
      | ~ v1_funct_2(E_319,u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0(D_317))
      | ~ v1_funct_1(E_319)
      | ~ l1_pre_topc(D_317)
      | ~ v2_pre_topc(D_317)
      | v2_struct_0(D_317)
      | ~ r3_tsep_1('#skF_3','#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_3')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_3')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_1333])).

tff(c_1347,plain,(
    ! [E_319,D_317] :
      ( v5_pre_topc(E_319,'#skF_3',D_317)
      | ~ m1_subset_1(k3_tmap_1('#skF_3',D_317,'#skF_3','#skF_5',E_319),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(D_317))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_3',D_317,'#skF_3','#skF_5',E_319),'#skF_5',D_317)
      | ~ v1_funct_2(k3_tmap_1('#skF_3',D_317,'#skF_3','#skF_5',E_319),u1_struct_0('#skF_5'),u1_struct_0(D_317))
      | ~ v1_funct_1(k3_tmap_1('#skF_3',D_317,'#skF_3','#skF_5',E_319))
      | ~ m1_subset_1(k3_tmap_1('#skF_3',D_317,'#skF_3','#skF_4',E_319),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(D_317))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_3',D_317,'#skF_3','#skF_4',E_319),'#skF_4',D_317)
      | ~ v1_funct_2(k3_tmap_1('#skF_3',D_317,'#skF_3','#skF_4',E_319),u1_struct_0('#skF_4'),u1_struct_0(D_317))
      | ~ v1_funct_1(k3_tmap_1('#skF_3',D_317,'#skF_3','#skF_4',E_319))
      | ~ m1_subset_1(E_319,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(D_317))))
      | ~ v1_funct_2(E_319,u1_struct_0('#skF_3'),u1_struct_0(D_317))
      | ~ v1_funct_1(E_319)
      | ~ l1_pre_topc(D_317)
      | ~ v2_pre_topc(D_317)
      | v2_struct_0(D_317)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_50,c_643,c_48,c_48,c_48,c_48,c_48,c_48,c_48,c_48,c_48,c_48,c_1343])).

tff(c_1349,plain,(
    ! [E_320,D_321] :
      ( v5_pre_topc(E_320,'#skF_3',D_321)
      | ~ m1_subset_1(k3_tmap_1('#skF_3',D_321,'#skF_3','#skF_5',E_320),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(D_321))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_3',D_321,'#skF_3','#skF_5',E_320),'#skF_5',D_321)
      | ~ v1_funct_2(k3_tmap_1('#skF_3',D_321,'#skF_3','#skF_5',E_320),u1_struct_0('#skF_5'),u1_struct_0(D_321))
      | ~ v1_funct_1(k3_tmap_1('#skF_3',D_321,'#skF_3','#skF_5',E_320))
      | ~ m1_subset_1(k3_tmap_1('#skF_3',D_321,'#skF_3','#skF_4',E_320),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(D_321))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_3',D_321,'#skF_3','#skF_4',E_320),'#skF_4',D_321)
      | ~ v1_funct_2(k3_tmap_1('#skF_3',D_321,'#skF_3','#skF_4',E_320),u1_struct_0('#skF_4'),u1_struct_0(D_321))
      | ~ v1_funct_1(k3_tmap_1('#skF_3',D_321,'#skF_3','#skF_4',E_320))
      | ~ m1_subset_1(E_320,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(D_321))))
      | ~ v1_funct_2(E_320,u1_struct_0('#skF_3'),u1_struct_0(D_321))
      | ~ v1_funct_1(E_320)
      | ~ l1_pre_topc(D_321)
      | ~ v2_pre_topc(D_321)
      | v2_struct_0(D_321) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_52,c_1347])).

tff(c_1352,plain,
    ( v5_pre_topc('#skF_7','#skF_3','#skF_6')
    | ~ m1_subset_1(k2_tmap_1('#skF_3','#skF_6','#skF_7','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_6'))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_6','#skF_3','#skF_5','#skF_7'),'#skF_5','#skF_6')
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_6','#skF_3','#skF_5','#skF_7'),u1_struct_0('#skF_5'),u1_struct_0('#skF_6'))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_6','#skF_3','#skF_5','#skF_7'))
    | ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_6','#skF_3','#skF_4','#skF_7'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_6'))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_6','#skF_3','#skF_4','#skF_7'),'#skF_4','#skF_6')
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_6','#skF_3','#skF_4','#skF_7'),u1_struct_0('#skF_4'),u1_struct_0('#skF_6'))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_6','#skF_3','#skF_4','#skF_7'))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_6'))))
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_3'),u1_struct_0('#skF_6'))
    | ~ v1_funct_1('#skF_7')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_879,c_1349])).

tff(c_1354,plain,
    ( v5_pre_topc('#skF_7','#skF_3','#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_649,c_645,c_642,c_655,c_659,c_653,c_966,c_663,c_966,c_661,c_966,c_667,c_966,c_651,c_879,c_665,c_879,c_657,c_879,c_669,c_1352])).

tff(c_1356,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_647,c_679,c_1354])).

tff(c_1358,plain,(
    ~ r1_tsep_1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_224])).

tff(c_1357,plain,(
    r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_224])).

tff(c_1387,plain,(
    ! [B_322,C_323,A_324] :
      ( r1_tsep_1(B_322,C_323)
      | ~ r3_tsep_1(A_324,B_322,C_323)
      | ~ m1_pre_topc(C_323,A_324)
      | v2_struct_0(C_323)
      | ~ m1_pre_topc(B_322,A_324)
      | v2_struct_0(B_322)
      | ~ l1_pre_topc(A_324)
      | ~ v2_pre_topc(A_324)
      | v2_struct_0(A_324) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_1390,plain,
    ( r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1357,c_1387])).

tff(c_1393,plain,
    ( r1_tsep_1('#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_50,c_1390])).

tff(c_1395,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_52,c_1358,c_1393])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:26:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.43/1.95  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.43/1.98  
% 5.43/1.98  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.43/1.98  %$ v5_pre_topc > v1_funct_2 > r3_tsep_1 > r1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 5.43/1.98  
% 5.43/1.98  %Foreground sorts:
% 5.43/1.98  
% 5.43/1.98  
% 5.43/1.98  %Background operators:
% 5.43/1.98  
% 5.43/1.98  
% 5.43/1.98  %Foreground operators:
% 5.43/1.98  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.43/1.98  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 5.43/1.98  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 5.43/1.98  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.43/1.98  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.43/1.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.43/1.98  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.43/1.98  tff('#skF_7', type, '#skF_7': $i).
% 5.43/1.98  tff('#skF_5', type, '#skF_5': $i).
% 5.43/1.98  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.43/1.98  tff('#skF_6', type, '#skF_6': $i).
% 5.43/1.98  tff('#skF_3', type, '#skF_3': $i).
% 5.43/1.98  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.43/1.98  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.43/1.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.43/1.98  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.43/1.98  tff('#skF_4', type, '#skF_4': $i).
% 5.43/1.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.43/1.98  tff(r3_tsep_1, type, r3_tsep_1: ($i * $i * $i) > $o).
% 5.43/1.98  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 5.43/1.98  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.43/1.98  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 5.43/1.98  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.43/1.98  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 5.43/1.98  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 5.43/1.98  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.43/1.98  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.43/1.98  
% 5.76/2.01  tff(f_215, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => ((A = k1_tsep_1(A, B, C)) => (r3_tsep_1(A, B, C) <=> (r1_tsep_1(B, C) & (![D]: (((~v2_struct_0(D) & v2_pre_topc(D)) & l1_pre_topc(D)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(D))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(D))))) => ((((((((v1_funct_1(k2_tmap_1(A, D, E, B)) & v1_funct_2(k2_tmap_1(A, D, E, B), u1_struct_0(B), u1_struct_0(D))) & v5_pre_topc(k2_tmap_1(A, D, E, B), B, D)) & m1_subset_1(k2_tmap_1(A, D, E, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(D))))) & v1_funct_1(k2_tmap_1(A, D, E, C))) & v1_funct_2(k2_tmap_1(A, D, E, C), u1_struct_0(C), u1_struct_0(D))) & v5_pre_topc(k2_tmap_1(A, D, E, C), C, D)) & m1_subset_1(k2_tmap_1(A, D, E, C), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(D))))) => (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(D))) & v5_pre_topc(E, A, D)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(D))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_tmap_1)).
% 5.76/2.01  tff(f_146, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (r3_tsep_1(A, B, C) <=> (r1_tsep_1(B, C) & (![D]: (((~v2_struct_0(D) & v2_pre_topc(D)) & l1_pre_topc(D)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(k1_tsep_1(A, B, C)), u1_struct_0(D))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, B, C)), u1_struct_0(D))))) => ((((((((v1_funct_1(k3_tmap_1(A, D, k1_tsep_1(A, B, C), B, E)) & v1_funct_2(k3_tmap_1(A, D, k1_tsep_1(A, B, C), B, E), u1_struct_0(B), u1_struct_0(D))) & v5_pre_topc(k3_tmap_1(A, D, k1_tsep_1(A, B, C), B, E), B, D)) & m1_subset_1(k3_tmap_1(A, D, k1_tsep_1(A, B, C), B, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(D))))) & v1_funct_1(k3_tmap_1(A, D, k1_tsep_1(A, B, C), C, E))) & v1_funct_2(k3_tmap_1(A, D, k1_tsep_1(A, B, C), C, E), u1_struct_0(C), u1_struct_0(D))) & v5_pre_topc(k3_tmap_1(A, D, k1_tsep_1(A, B, C), C, E), C, D)) & m1_subset_1(k3_tmap_1(A, D, k1_tsep_1(A, B, C), C, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(D))))) => (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(k1_tsep_1(A, B, C)), u1_struct_0(D))) & v5_pre_topc(E, k1_tsep_1(A, B, C), D)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, B, C)), u1_struct_0(D)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t135_tmap_1)).
% 5.76/2.01  tff(f_52, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 5.76/2.01  tff(f_150, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 5.76/2.01  tff(f_84, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 5.76/2.01  tff(c_62, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_215])).
% 5.76/2.01  tff(c_56, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_215])).
% 5.76/2.01  tff(c_52, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_215])).
% 5.76/2.01  tff(c_224, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | r1_tsep_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_215])).
% 5.76/2.01  tff(c_260, plain, (r1_tsep_1('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_224])).
% 5.76/2.01  tff(c_88, plain, (v1_funct_1('#skF_7') | ~r1_tsep_1('#skF_4', '#skF_5') | ~r3_tsep_1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_215])).
% 5.76/2.01  tff(c_262, plain, (v1_funct_1('#skF_7') | ~r3_tsep_1('#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_260, c_88])).
% 5.76/2.01  tff(c_263, plain, (~r3_tsep_1('#skF_3', '#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_262])).
% 5.76/2.01  tff(c_60, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_215])).
% 5.76/2.01  tff(c_58, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_215])).
% 5.76/2.01  tff(c_54, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_215])).
% 5.76/2.01  tff(c_50, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_215])).
% 5.76/2.01  tff(c_30, plain, (![A_47, B_75, C_89]: (l1_pre_topc('#skF_1'(A_47, B_75, C_89)) | r3_tsep_1(A_47, B_75, C_89) | ~r1_tsep_1(B_75, C_89) | ~m1_pre_topc(C_89, A_47) | v2_struct_0(C_89) | ~m1_pre_topc(B_75, A_47) | v2_struct_0(B_75) | ~l1_pre_topc(A_47) | ~v2_pre_topc(A_47) | v2_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.76/2.01  tff(c_28, plain, (![A_47, B_75, C_89]: (v1_funct_1('#skF_2'(A_47, B_75, C_89)) | r3_tsep_1(A_47, B_75, C_89) | ~r1_tsep_1(B_75, C_89) | ~m1_pre_topc(C_89, A_47) | v2_struct_0(C_89) | ~m1_pre_topc(B_75, A_47) | v2_struct_0(B_75) | ~l1_pre_topc(A_47) | ~v2_pre_topc(A_47) | v2_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.76/2.01  tff(c_32, plain, (![A_47, B_75, C_89]: (v2_pre_topc('#skF_1'(A_47, B_75, C_89)) | r3_tsep_1(A_47, B_75, C_89) | ~r1_tsep_1(B_75, C_89) | ~m1_pre_topc(C_89, A_47) | v2_struct_0(C_89) | ~m1_pre_topc(B_75, A_47) | v2_struct_0(B_75) | ~l1_pre_topc(A_47) | ~v2_pre_topc(A_47) | v2_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.76/2.01  tff(c_48, plain, (k1_tsep_1('#skF_3', '#skF_4', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_215])).
% 5.76/2.01  tff(c_299, plain, (![A_169, B_170, C_171]: (v1_funct_2('#skF_2'(A_169, B_170, C_171), u1_struct_0(k1_tsep_1(A_169, B_170, C_171)), u1_struct_0('#skF_1'(A_169, B_170, C_171))) | r3_tsep_1(A_169, B_170, C_171) | ~r1_tsep_1(B_170, C_171) | ~m1_pre_topc(C_171, A_169) | v2_struct_0(C_171) | ~m1_pre_topc(B_170, A_169) | v2_struct_0(B_170) | ~l1_pre_topc(A_169) | ~v2_pre_topc(A_169) | v2_struct_0(A_169))), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.76/2.01  tff(c_302, plain, (v1_funct_2('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_48, c_299])).
% 5.76/2.01  tff(c_304, plain, (v1_funct_2('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_50, c_260, c_302])).
% 5.76/2.01  tff(c_305, plain, (v1_funct_2('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_52, c_263, c_304])).
% 5.76/2.01  tff(c_322, plain, (![A_178, B_179, C_180]: (m1_subset_1('#skF_2'(A_178, B_179, C_180), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_178, B_179, C_180)), u1_struct_0('#skF_1'(A_178, B_179, C_180))))) | r3_tsep_1(A_178, B_179, C_180) | ~r1_tsep_1(B_179, C_180) | ~m1_pre_topc(C_180, A_178) | v2_struct_0(C_180) | ~m1_pre_topc(B_179, A_178) | v2_struct_0(B_179) | ~l1_pre_topc(A_178) | ~v2_pre_topc(A_178) | v2_struct_0(A_178))), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.76/2.01  tff(c_325, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_48, c_322])).
% 5.76/2.01  tff(c_327, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_50, c_260, c_325])).
% 5.76/2.01  tff(c_328, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')))))), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_52, c_263, c_327])).
% 5.76/2.01  tff(c_343, plain, (![A_187, B_188, C_189, D_190]: (k2_partfun1(u1_struct_0(A_187), u1_struct_0(B_188), C_189, u1_struct_0(D_190))=k2_tmap_1(A_187, B_188, C_189, D_190) | ~m1_pre_topc(D_190, A_187) | ~m1_subset_1(C_189, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_187), u1_struct_0(B_188)))) | ~v1_funct_2(C_189, u1_struct_0(A_187), u1_struct_0(B_188)) | ~v1_funct_1(C_189) | ~l1_pre_topc(B_188) | ~v2_pre_topc(B_188) | v2_struct_0(B_188) | ~l1_pre_topc(A_187) | ~v2_pre_topc(A_187) | v2_struct_0(A_187))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.76/2.01  tff(c_345, plain, (![D_190]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(D_190))=k2_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), D_190) | ~m1_pre_topc(D_190, '#skF_3') | ~v1_funct_2('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_328, c_343])).
% 5.76/2.01  tff(c_350, plain, (![D_190]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(D_190))=k2_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), D_190) | ~m1_pre_topc(D_190, '#skF_3') | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_305, c_345])).
% 5.76/2.01  tff(c_351, plain, (![D_190]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(D_190))=k2_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), D_190) | ~m1_pre_topc(D_190, '#skF_3') | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_62, c_350])).
% 5.76/2.01  tff(c_426, plain, (~v2_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_351])).
% 5.76/2.01  tff(c_429, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_32, c_426])).
% 5.76/2.01  tff(c_432, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_50, c_260, c_429])).
% 5.76/2.01  tff(c_434, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_52, c_263, c_432])).
% 5.76/2.01  tff(c_435, plain, (![D_190]: (~l1_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(D_190))=k2_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), D_190) | ~m1_pre_topc(D_190, '#skF_3'))), inference(splitRight, [status(thm)], [c_351])).
% 5.76/2.01  tff(c_439, plain, (~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_435])).
% 5.76/2.01  tff(c_442, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_28, c_439])).
% 5.76/2.01  tff(c_445, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_50, c_260, c_442])).
% 5.76/2.01  tff(c_447, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_52, c_263, c_445])).
% 5.76/2.01  tff(c_448, plain, (![D_190]: (~l1_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(D_190))=k2_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), D_190) | ~m1_pre_topc(D_190, '#skF_3'))), inference(splitRight, [status(thm)], [c_435])).
% 5.76/2.01  tff(c_450, plain, (~l1_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_448])).
% 5.76/2.01  tff(c_464, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_30, c_450])).
% 5.76/2.01  tff(c_467, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_50, c_260, c_464])).
% 5.76/2.01  tff(c_469, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_52, c_263, c_467])).
% 5.76/2.01  tff(c_470, plain, (![D_190]: (v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(D_190))=k2_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), D_190) | ~m1_pre_topc(D_190, '#skF_3'))), inference(splitRight, [status(thm)], [c_448])).
% 5.76/2.01  tff(c_472, plain, (v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_470])).
% 5.76/2.01  tff(c_34, plain, (![A_47, B_75, C_89]: (~v2_struct_0('#skF_1'(A_47, B_75, C_89)) | r3_tsep_1(A_47, B_75, C_89) | ~r1_tsep_1(B_75, C_89) | ~m1_pre_topc(C_89, A_47) | v2_struct_0(C_89) | ~m1_pre_topc(B_75, A_47) | v2_struct_0(B_75) | ~l1_pre_topc(A_47) | ~v2_pre_topc(A_47) | v2_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.76/2.01  tff(c_477, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_472, c_34])).
% 5.76/2.01  tff(c_480, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_50, c_260, c_477])).
% 5.76/2.01  tff(c_482, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_52, c_263, c_480])).
% 5.76/2.01  tff(c_484, plain, (~v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_470])).
% 5.76/2.01  tff(c_449, plain, (v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_435])).
% 5.76/2.01  tff(c_581, plain, (![A_216, B_217, C_218]: (~m1_subset_1('#skF_2'(A_216, B_217, C_218), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_216, B_217, C_218)), u1_struct_0('#skF_1'(A_216, B_217, C_218))))) | ~v5_pre_topc('#skF_2'(A_216, B_217, C_218), k1_tsep_1(A_216, B_217, C_218), '#skF_1'(A_216, B_217, C_218)) | ~v1_funct_2('#skF_2'(A_216, B_217, C_218), u1_struct_0(k1_tsep_1(A_216, B_217, C_218)), u1_struct_0('#skF_1'(A_216, B_217, C_218))) | ~v1_funct_1('#skF_2'(A_216, B_217, C_218)) | r3_tsep_1(A_216, B_217, C_218) | ~r1_tsep_1(B_217, C_218) | ~m1_pre_topc(C_218, A_216) | v2_struct_0(C_218) | ~m1_pre_topc(B_217, A_216) | v2_struct_0(B_217) | ~l1_pre_topc(A_216) | ~v2_pre_topc(A_216) | v2_struct_0(A_216))), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.76/2.01  tff(c_587, plain, (~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v5_pre_topc('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_48, c_581])).
% 5.76/2.01  tff(c_590, plain, (~v5_pre_topc('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_50, c_260, c_449, c_305, c_48, c_48, c_328, c_587])).
% 5.76/2.01  tff(c_591, plain, (~v5_pre_topc('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_52, c_263, c_590])).
% 5.76/2.01  tff(c_436, plain, (v2_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_351])).
% 5.76/2.01  tff(c_471, plain, (l1_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_448])).
% 5.76/2.01  tff(c_46, plain, (![A_100]: (m1_pre_topc(A_100, A_100) | ~l1_pre_topc(A_100))), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.76/2.01  tff(c_395, plain, (![A_207, D_205, C_206, B_203, E_204]: (k3_tmap_1(A_207, B_203, C_206, D_205, E_204)=k2_partfun1(u1_struct_0(C_206), u1_struct_0(B_203), E_204, u1_struct_0(D_205)) | ~m1_pre_topc(D_205, C_206) | ~m1_subset_1(E_204, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_206), u1_struct_0(B_203)))) | ~v1_funct_2(E_204, u1_struct_0(C_206), u1_struct_0(B_203)) | ~v1_funct_1(E_204) | ~m1_pre_topc(D_205, A_207) | ~m1_pre_topc(C_206, A_207) | ~l1_pre_topc(B_203) | ~v2_pre_topc(B_203) | v2_struct_0(B_203) | ~l1_pre_topc(A_207) | ~v2_pre_topc(A_207) | v2_struct_0(A_207))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.76/2.01  tff(c_403, plain, (![A_207, D_205]: (k3_tmap_1(A_207, '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_3', D_205, '#skF_2'('#skF_3', '#skF_4', '#skF_5'))=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(D_205)) | ~m1_pre_topc(D_205, '#skF_3') | ~v1_funct_2('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~m1_pre_topc(D_205, A_207) | ~m1_pre_topc('#skF_3', A_207) | ~l1_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~l1_pre_topc(A_207) | ~v2_pre_topc(A_207) | v2_struct_0(A_207))), inference(resolution, [status(thm)], [c_328, c_395])).
% 5.76/2.01  tff(c_413, plain, (![A_207, D_205]: (k3_tmap_1(A_207, '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_3', D_205, '#skF_2'('#skF_3', '#skF_4', '#skF_5'))=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(D_205)) | ~m1_pre_topc(D_205, '#skF_3') | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~m1_pre_topc(D_205, A_207) | ~m1_pre_topc('#skF_3', A_207) | ~l1_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~l1_pre_topc(A_207) | ~v2_pre_topc(A_207) | v2_struct_0(A_207))), inference(demodulation, [status(thm), theory('equality')], [c_305, c_403])).
% 5.76/2.01  tff(c_495, plain, (![A_207, D_205]: (k3_tmap_1(A_207, '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_3', D_205, '#skF_2'('#skF_3', '#skF_4', '#skF_5'))=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(D_205)) | ~m1_pre_topc(D_205, '#skF_3') | ~m1_pre_topc(D_205, A_207) | ~m1_pre_topc('#skF_3', A_207) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~l1_pre_topc(A_207) | ~v2_pre_topc(A_207) | v2_struct_0(A_207))), inference(demodulation, [status(thm), theory('equality')], [c_436, c_471, c_449, c_413])).
% 5.76/2.01  tff(c_497, plain, (![A_212, D_213]: (k3_tmap_1(A_212, '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_3', D_213, '#skF_2'('#skF_3', '#skF_4', '#skF_5'))=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(D_213)) | ~m1_pre_topc(D_213, '#skF_3') | ~m1_pre_topc(D_213, A_212) | ~m1_pre_topc('#skF_3', A_212) | ~l1_pre_topc(A_212) | ~v2_pre_topc(A_212) | v2_struct_0(A_212))), inference(negUnitSimplification, [status(thm)], [c_484, c_495])).
% 5.76/2.01  tff(c_483, plain, (![D_190]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(D_190))=k2_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), D_190) | ~m1_pre_topc(D_190, '#skF_3'))), inference(splitRight, [status(thm)], [c_470])).
% 5.76/2.01  tff(c_518, plain, (![A_214, D_215]: (k3_tmap_1(A_214, '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_3', D_215, '#skF_2'('#skF_3', '#skF_4', '#skF_5'))=k2_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), D_215) | ~m1_pre_topc(D_215, '#skF_3') | ~m1_pre_topc(D_215, '#skF_3') | ~m1_pre_topc(D_215, A_214) | ~m1_pre_topc('#skF_3', A_214) | ~l1_pre_topc(A_214) | ~v2_pre_topc(A_214) | v2_struct_0(A_214))), inference(superposition, [status(thm), theory('equality')], [c_497, c_483])).
% 5.76/2.01  tff(c_313, plain, (![A_175, B_176, C_177]: (v1_funct_1(k3_tmap_1(A_175, '#skF_1'(A_175, B_176, C_177), k1_tsep_1(A_175, B_176, C_177), C_177, '#skF_2'(A_175, B_176, C_177))) | r3_tsep_1(A_175, B_176, C_177) | ~r1_tsep_1(B_176, C_177) | ~m1_pre_topc(C_177, A_175) | v2_struct_0(C_177) | ~m1_pre_topc(B_176, A_175) | v2_struct_0(B_176) | ~l1_pre_topc(A_175) | ~v2_pre_topc(A_175) | v2_struct_0(A_175))), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.76/2.01  tff(c_316, plain, (v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_3', '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_48, c_313])).
% 5.76/2.01  tff(c_318, plain, (v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_3', '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_50, c_260, c_316])).
% 5.76/2.01  tff(c_319, plain, (v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_3', '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_52, c_263, c_318])).
% 5.76/2.01  tff(c_545, plain, (v1_funct_1(k2_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_5')) | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_518, c_319])).
% 5.76/2.01  tff(c_575, plain, (v1_funct_1(k2_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_5')) | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_50, c_50, c_50, c_545])).
% 5.76/2.01  tff(c_576, plain, (v1_funct_1(k2_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_5')) | ~m1_pre_topc('#skF_3', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_62, c_575])).
% 5.76/2.01  tff(c_592, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_576])).
% 5.76/2.01  tff(c_595, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_46, c_592])).
% 5.76/2.01  tff(c_599, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_595])).
% 5.76/2.01  tff(c_601, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_576])).
% 5.76/2.01  tff(c_306, plain, (![A_172, B_173, C_174]: (v1_funct_1(k3_tmap_1(A_172, '#skF_1'(A_172, B_173, C_174), k1_tsep_1(A_172, B_173, C_174), B_173, '#skF_2'(A_172, B_173, C_174))) | r3_tsep_1(A_172, B_173, C_174) | ~r1_tsep_1(B_173, C_174) | ~m1_pre_topc(C_174, A_172) | v2_struct_0(C_174) | ~m1_pre_topc(B_173, A_172) | v2_struct_0(B_173) | ~l1_pre_topc(A_172) | ~v2_pre_topc(A_172) | v2_struct_0(A_172))), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.76/2.01  tff(c_309, plain, (v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_48, c_306])).
% 5.76/2.01  tff(c_311, plain, (v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_50, c_260, c_309])).
% 5.76/2.01  tff(c_312, plain, (v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_52, c_263, c_311])).
% 5.76/2.01  tff(c_548, plain, (v1_funct_1(k2_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_518, c_312])).
% 5.76/2.01  tff(c_578, plain, (v1_funct_1(k2_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_54, c_54, c_548])).
% 5.76/2.01  tff(c_579, plain, (v1_funct_1(k2_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_62, c_578])).
% 5.76/2.01  tff(c_605, plain, (v1_funct_1(k2_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_601, c_579])).
% 5.76/2.01  tff(c_353, plain, (![A_191, B_192, C_193]: (v1_funct_2(k3_tmap_1(A_191, '#skF_1'(A_191, B_192, C_193), k1_tsep_1(A_191, B_192, C_193), B_192, '#skF_2'(A_191, B_192, C_193)), u1_struct_0(B_192), u1_struct_0('#skF_1'(A_191, B_192, C_193))) | r3_tsep_1(A_191, B_192, C_193) | ~r1_tsep_1(B_192, C_193) | ~m1_pre_topc(C_193, A_191) | v2_struct_0(C_193) | ~m1_pre_topc(B_192, A_191) | v2_struct_0(B_192) | ~l1_pre_topc(A_191) | ~v2_pre_topc(A_191) | v2_struct_0(A_191))), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.76/2.01  tff(c_356, plain, (v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_48, c_353])).
% 5.76/2.01  tff(c_358, plain, (v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_50, c_260, c_356])).
% 5.76/2.01  tff(c_359, plain, (v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_52, c_263, c_358])).
% 5.76/2.01  tff(c_536, plain, (v1_funct_2(k2_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~m1_pre_topc('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_518, c_359])).
% 5.76/2.01  tff(c_566, plain, (v1_funct_2(k2_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_54, c_54, c_536])).
% 5.76/2.01  tff(c_567, plain, (v1_funct_2(k2_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~m1_pre_topc('#skF_3', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_62, c_566])).
% 5.76/2.01  tff(c_615, plain, (v1_funct_2(k2_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_601, c_567])).
% 5.76/2.01  tff(c_329, plain, (![A_181, B_182, C_183]: (v5_pre_topc(k3_tmap_1(A_181, '#skF_1'(A_181, B_182, C_183), k1_tsep_1(A_181, B_182, C_183), B_182, '#skF_2'(A_181, B_182, C_183)), B_182, '#skF_1'(A_181, B_182, C_183)) | r3_tsep_1(A_181, B_182, C_183) | ~r1_tsep_1(B_182, C_183) | ~m1_pre_topc(C_183, A_181) | v2_struct_0(C_183) | ~m1_pre_topc(B_182, A_181) | v2_struct_0(B_182) | ~l1_pre_topc(A_181) | ~v2_pre_topc(A_181) | v2_struct_0(A_181))), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.76/2.01  tff(c_332, plain, (v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_48, c_329])).
% 5.76/2.01  tff(c_334, plain, (v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_50, c_260, c_332])).
% 5.76/2.01  tff(c_335, plain, (v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_52, c_263, c_334])).
% 5.76/2.01  tff(c_542, plain, (v5_pre_topc(k2_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_4'), '#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~m1_pre_topc('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_518, c_335])).
% 5.76/2.01  tff(c_572, plain, (v5_pre_topc(k2_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_4'), '#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_54, c_54, c_542])).
% 5.76/2.01  tff(c_573, plain, (v5_pre_topc(k2_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_4'), '#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~m1_pre_topc('#skF_3', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_62, c_572])).
% 5.76/2.01  tff(c_609, plain, (v5_pre_topc(k2_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_4'), '#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_601, c_573])).
% 5.76/2.01  tff(c_600, plain, (v1_funct_1(k2_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_5'))), inference(splitRight, [status(thm)], [c_576])).
% 5.76/2.01  tff(c_362, plain, (![A_194, B_195, C_196]: (v1_funct_2(k3_tmap_1(A_194, '#skF_1'(A_194, B_195, C_196), k1_tsep_1(A_194, B_195, C_196), C_196, '#skF_2'(A_194, B_195, C_196)), u1_struct_0(C_196), u1_struct_0('#skF_1'(A_194, B_195, C_196))) | r3_tsep_1(A_194, B_195, C_196) | ~r1_tsep_1(B_195, C_196) | ~m1_pre_topc(C_196, A_194) | v2_struct_0(C_196) | ~m1_pre_topc(B_195, A_194) | v2_struct_0(B_195) | ~l1_pre_topc(A_194) | ~v2_pre_topc(A_194) | v2_struct_0(A_194))), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.76/2.01  tff(c_365, plain, (v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_3', '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_48, c_362])).
% 5.76/2.01  tff(c_367, plain, (v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_3', '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_50, c_260, c_365])).
% 5.76/2.01  tff(c_368, plain, (v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_3', '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_52, c_263, c_367])).
% 5.76/2.01  tff(c_533, plain, (v1_funct_2(k2_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_518, c_368])).
% 5.76/2.01  tff(c_563, plain, (v1_funct_2(k2_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_50, c_50, c_50, c_533])).
% 5.76/2.01  tff(c_564, plain, (v1_funct_2(k2_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~m1_pre_topc('#skF_3', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_62, c_563])).
% 5.76/2.01  tff(c_613, plain, (v1_funct_2(k2_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_601, c_564])).
% 5.76/2.01  tff(c_336, plain, (![A_184, B_185, C_186]: (v5_pre_topc(k3_tmap_1(A_184, '#skF_1'(A_184, B_185, C_186), k1_tsep_1(A_184, B_185, C_186), C_186, '#skF_2'(A_184, B_185, C_186)), C_186, '#skF_1'(A_184, B_185, C_186)) | r3_tsep_1(A_184, B_185, C_186) | ~r1_tsep_1(B_185, C_186) | ~m1_pre_topc(C_186, A_184) | v2_struct_0(C_186) | ~m1_pre_topc(B_185, A_184) | v2_struct_0(B_185) | ~l1_pre_topc(A_184) | ~v2_pre_topc(A_184) | v2_struct_0(A_184))), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.76/2.01  tff(c_339, plain, (v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_3', '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_5', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_48, c_336])).
% 5.76/2.01  tff(c_341, plain, (v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_3', '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_5', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_50, c_260, c_339])).
% 5.76/2.01  tff(c_342, plain, (v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_3', '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_5', '#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_52, c_263, c_341])).
% 5.76/2.01  tff(c_539, plain, (v5_pre_topc(k2_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_5'), '#skF_5', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_518, c_342])).
% 5.76/2.01  tff(c_569, plain, (v5_pre_topc(k2_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_5'), '#skF_5', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_50, c_50, c_50, c_539])).
% 5.76/2.01  tff(c_570, plain, (v5_pre_topc(k2_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_5'), '#skF_5', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~m1_pre_topc('#skF_3', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_62, c_569])).
% 5.76/2.01  tff(c_607, plain, (v5_pre_topc(k2_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_5'), '#skF_5', '#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_601, c_570])).
% 5.76/2.01  tff(c_385, plain, (![A_200, B_201, C_202]: (m1_subset_1(k3_tmap_1(A_200, '#skF_1'(A_200, B_201, C_202), k1_tsep_1(A_200, B_201, C_202), C_202, '#skF_2'(A_200, B_201, C_202)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_202), u1_struct_0('#skF_1'(A_200, B_201, C_202))))) | r3_tsep_1(A_200, B_201, C_202) | ~r1_tsep_1(B_201, C_202) | ~m1_pre_topc(C_202, A_200) | v2_struct_0(C_202) | ~m1_pre_topc(B_201, A_200) | v2_struct_0(B_201) | ~l1_pre_topc(A_200) | ~v2_pre_topc(A_200) | v2_struct_0(A_200))), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.76/2.01  tff(c_390, plain, (m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_3', '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_48, c_385])).
% 5.76/2.01  tff(c_393, plain, (m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_3', '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_50, c_260, c_390])).
% 5.76/2.01  tff(c_394, plain, (m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_3', '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')))))), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_52, c_263, c_393])).
% 5.76/2.01  tff(c_527, plain, (m1_subset_1(k2_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_518, c_394])).
% 5.76/2.01  tff(c_557, plain, (m1_subset_1(k2_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_50, c_50, c_50, c_527])).
% 5.76/2.01  tff(c_558, plain, (m1_subset_1(k2_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~m1_pre_topc('#skF_3', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_62, c_557])).
% 5.76/2.01  tff(c_617, plain, (m1_subset_1(k2_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')))))), inference(demodulation, [status(thm), theory('equality')], [c_601, c_558])).
% 5.76/2.01  tff(c_128, plain, (![E_150, D_148]: (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v5_pre_topc(E_150, '#skF_3', D_148) | ~m1_subset_1(k2_tmap_1('#skF_3', D_148, E_150, '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(D_148)))) | ~v5_pre_topc(k2_tmap_1('#skF_3', D_148, E_150, '#skF_5'), '#skF_5', D_148) | ~v1_funct_2(k2_tmap_1('#skF_3', D_148, E_150, '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0(D_148)) | ~v1_funct_1(k2_tmap_1('#skF_3', D_148, E_150, '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_3', D_148, E_150, '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(D_148)))) | ~v5_pre_topc(k2_tmap_1('#skF_3', D_148, E_150, '#skF_4'), '#skF_4', D_148) | ~v1_funct_2(k2_tmap_1('#skF_3', D_148, E_150, '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0(D_148)) | ~v1_funct_1(k2_tmap_1('#skF_3', D_148, E_150, '#skF_4')) | ~m1_subset_1(E_150, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(D_148)))) | ~v1_funct_2(E_150, u1_struct_0('#skF_3'), u1_struct_0(D_148)) | ~v1_funct_1(E_150) | ~l1_pre_topc(D_148) | ~v2_pre_topc(D_148) | v2_struct_0(D_148))), inference(cnfTransformation, [status(thm)], [f_215])).
% 5.76/2.01  tff(c_294, plain, (![E_150, D_148]: (v5_pre_topc(E_150, '#skF_3', D_148) | ~m1_subset_1(k2_tmap_1('#skF_3', D_148, E_150, '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(D_148)))) | ~v5_pre_topc(k2_tmap_1('#skF_3', D_148, E_150, '#skF_5'), '#skF_5', D_148) | ~v1_funct_2(k2_tmap_1('#skF_3', D_148, E_150, '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0(D_148)) | ~v1_funct_1(k2_tmap_1('#skF_3', D_148, E_150, '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_3', D_148, E_150, '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(D_148)))) | ~v5_pre_topc(k2_tmap_1('#skF_3', D_148, E_150, '#skF_4'), '#skF_4', D_148) | ~v1_funct_2(k2_tmap_1('#skF_3', D_148, E_150, '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0(D_148)) | ~v1_funct_1(k2_tmap_1('#skF_3', D_148, E_150, '#skF_4')) | ~m1_subset_1(E_150, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(D_148)))) | ~v1_funct_2(E_150, u1_struct_0('#skF_3'), u1_struct_0(D_148)) | ~v1_funct_1(E_150) | ~l1_pre_topc(D_148) | ~v2_pre_topc(D_148) | v2_struct_0(D_148))), inference(negUnitSimplification, [status(thm)], [c_263, c_128])).
% 5.76/2.01  tff(c_624, plain, (v5_pre_topc('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v5_pre_topc(k2_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_5'), '#skF_5', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2(k2_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k2_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v5_pre_topc(k2_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_4'), '#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2(k2_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k2_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_4')) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_2('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_617, c_294])).
% 5.76/2.01  tff(c_635, plain, (v5_pre_topc('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_436, c_471, c_449, c_305, c_328, c_605, c_615, c_609, c_600, c_613, c_607, c_624])).
% 5.76/2.01  tff(c_636, plain, (~m1_subset_1(k2_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')))))), inference(negUnitSimplification, [status(thm)], [c_484, c_591, c_635])).
% 5.76/2.01  tff(c_369, plain, (![A_197, B_198, C_199]: (m1_subset_1(k3_tmap_1(A_197, '#skF_1'(A_197, B_198, C_199), k1_tsep_1(A_197, B_198, C_199), B_198, '#skF_2'(A_197, B_198, C_199)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_198), u1_struct_0('#skF_1'(A_197, B_198, C_199))))) | r3_tsep_1(A_197, B_198, C_199) | ~r1_tsep_1(B_198, C_199) | ~m1_pre_topc(C_199, A_197) | v2_struct_0(C_199) | ~m1_pre_topc(B_198, A_197) | v2_struct_0(B_198) | ~l1_pre_topc(A_197) | ~v2_pre_topc(A_197) | v2_struct_0(A_197))), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.76/2.01  tff(c_374, plain, (m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_48, c_369])).
% 5.76/2.01  tff(c_377, plain, (m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_50, c_260, c_374])).
% 5.76/2.01  tff(c_378, plain, (m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')))))), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_52, c_263, c_377])).
% 5.76/2.01  tff(c_530, plain, (m1_subset_1(k2_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~m1_pre_topc('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_518, c_378])).
% 5.76/2.01  tff(c_560, plain, (m1_subset_1(k2_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_54, c_54, c_530])).
% 5.76/2.01  tff(c_561, plain, (m1_subset_1(k2_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~m1_pre_topc('#skF_3', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_62, c_560])).
% 5.76/2.01  tff(c_640, plain, (m1_subset_1(k2_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')))))), inference(demodulation, [status(thm), theory('equality')], [c_601, c_561])).
% 5.76/2.01  tff(c_641, plain, $false, inference(negUnitSimplification, [status(thm)], [c_636, c_640])).
% 5.76/2.01  tff(c_643, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_262])).
% 5.76/2.01  tff(c_94, plain, (~v2_struct_0('#skF_6') | ~r1_tsep_1('#skF_4', '#skF_5') | ~r3_tsep_1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_215])).
% 5.76/2.01  tff(c_647, plain, (~v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_643, c_260, c_94])).
% 5.76/2.01  tff(c_642, plain, (v1_funct_1('#skF_7')), inference(splitRight, [status(thm)], [c_262])).
% 5.76/2.01  tff(c_86, plain, (v1_funct_2('#skF_7', u1_struct_0('#skF_3'), u1_struct_0('#skF_6')) | ~r1_tsep_1('#skF_4', '#skF_5') | ~r3_tsep_1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_215])).
% 5.76/2.01  tff(c_655, plain, (v1_funct_2('#skF_7', u1_struct_0('#skF_3'), u1_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_643, c_260, c_86])).
% 5.76/2.01  tff(c_84, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_6')))) | ~r1_tsep_1('#skF_4', '#skF_5') | ~r3_tsep_1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_215])).
% 5.76/2.01  tff(c_659, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_643, c_260, c_84])).
% 5.76/2.01  tff(c_66, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_6')))) | ~v5_pre_topc('#skF_7', '#skF_3', '#skF_6') | ~v1_funct_2('#skF_7', u1_struct_0('#skF_3'), u1_struct_0('#skF_6')) | ~v1_funct_1('#skF_7') | ~r1_tsep_1('#skF_4', '#skF_5') | ~r3_tsep_1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_215])).
% 5.76/2.01  tff(c_679, plain, (~v5_pre_topc('#skF_7', '#skF_3', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_643, c_260, c_642, c_655, c_659, c_66])).
% 5.76/2.01  tff(c_92, plain, (v2_pre_topc('#skF_6') | ~r1_tsep_1('#skF_4', '#skF_5') | ~r3_tsep_1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_215])).
% 5.76/2.01  tff(c_649, plain, (v2_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_643, c_260, c_92])).
% 5.76/2.01  tff(c_90, plain, (l1_pre_topc('#skF_6') | ~r1_tsep_1('#skF_4', '#skF_5') | ~r3_tsep_1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_215])).
% 5.76/2.01  tff(c_645, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_643, c_260, c_90])).
% 5.76/2.01  tff(c_82, plain, (v1_funct_1(k2_tmap_1('#skF_3', '#skF_6', '#skF_7', '#skF_4')) | ~r1_tsep_1('#skF_4', '#skF_5') | ~r3_tsep_1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_215])).
% 5.76/2.01  tff(c_653, plain, (v1_funct_1(k2_tmap_1('#skF_3', '#skF_6', '#skF_7', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_643, c_260, c_82])).
% 5.76/2.01  tff(c_798, plain, (![E_270, B_269, D_271, A_273, C_272]: (k3_tmap_1(A_273, B_269, C_272, D_271, E_270)=k2_partfun1(u1_struct_0(C_272), u1_struct_0(B_269), E_270, u1_struct_0(D_271)) | ~m1_pre_topc(D_271, C_272) | ~m1_subset_1(E_270, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_272), u1_struct_0(B_269)))) | ~v1_funct_2(E_270, u1_struct_0(C_272), u1_struct_0(B_269)) | ~v1_funct_1(E_270) | ~m1_pre_topc(D_271, A_273) | ~m1_pre_topc(C_272, A_273) | ~l1_pre_topc(B_269) | ~v2_pre_topc(B_269) | v2_struct_0(B_269) | ~l1_pre_topc(A_273) | ~v2_pre_topc(A_273) | v2_struct_0(A_273))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.76/2.01  tff(c_810, plain, (![A_273, D_271]: (k3_tmap_1(A_273, '#skF_6', '#skF_3', D_271, '#skF_7')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_6'), '#skF_7', u1_struct_0(D_271)) | ~m1_pre_topc(D_271, '#skF_3') | ~v1_funct_2('#skF_7', u1_struct_0('#skF_3'), u1_struct_0('#skF_6')) | ~v1_funct_1('#skF_7') | ~m1_pre_topc(D_271, A_273) | ~m1_pre_topc('#skF_3', A_273) | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | ~l1_pre_topc(A_273) | ~v2_pre_topc(A_273) | v2_struct_0(A_273))), inference(resolution, [status(thm)], [c_659, c_798])).
% 5.76/2.01  tff(c_824, plain, (![A_273, D_271]: (k3_tmap_1(A_273, '#skF_6', '#skF_3', D_271, '#skF_7')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_6'), '#skF_7', u1_struct_0(D_271)) | ~m1_pre_topc(D_271, '#skF_3') | ~m1_pre_topc(D_271, A_273) | ~m1_pre_topc('#skF_3', A_273) | v2_struct_0('#skF_6') | ~l1_pre_topc(A_273) | ~v2_pre_topc(A_273) | v2_struct_0(A_273))), inference(demodulation, [status(thm), theory('equality')], [c_649, c_645, c_642, c_655, c_810])).
% 5.76/2.01  tff(c_826, plain, (![A_274, D_275]: (k3_tmap_1(A_274, '#skF_6', '#skF_3', D_275, '#skF_7')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_6'), '#skF_7', u1_struct_0(D_275)) | ~m1_pre_topc(D_275, '#skF_3') | ~m1_pre_topc(D_275, A_274) | ~m1_pre_topc('#skF_3', A_274) | ~l1_pre_topc(A_274) | ~v2_pre_topc(A_274) | v2_struct_0(A_274))), inference(negUnitSimplification, [status(thm)], [c_647, c_824])).
% 5.76/2.01  tff(c_830, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_6'), '#skF_7', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_3', '#skF_6', '#skF_3', '#skF_5', '#skF_7') | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_826])).
% 5.76/2.01  tff(c_836, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_6'), '#skF_7', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_3', '#skF_6', '#skF_3', '#skF_5', '#skF_7') | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_50, c_830])).
% 5.76/2.01  tff(c_837, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_6'), '#skF_7', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_3', '#skF_6', '#skF_3', '#skF_5', '#skF_7') | ~m1_pre_topc('#skF_3', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_62, c_836])).
% 5.76/2.01  tff(c_842, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_837])).
% 5.76/2.01  tff(c_856, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_46, c_842])).
% 5.76/2.01  tff(c_860, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_856])).
% 5.76/2.01  tff(c_862, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_837])).
% 5.76/2.01  tff(c_832, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_6'), '#skF_7', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_3', '#skF_6', '#skF_3', '#skF_4', '#skF_7') | ~m1_pre_topc('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_54, c_826])).
% 5.76/2.01  tff(c_840, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_6'), '#skF_7', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_3', '#skF_6', '#skF_3', '#skF_4', '#skF_7') | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_832])).
% 5.76/2.01  tff(c_841, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_6'), '#skF_7', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_3', '#skF_6', '#skF_3', '#skF_4', '#skF_7') | ~m1_pre_topc('#skF_3', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_62, c_840])).
% 5.76/2.01  tff(c_955, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_6'), '#skF_7', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_3', '#skF_6', '#skF_3', '#skF_4', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_862, c_841])).
% 5.76/2.01  tff(c_729, plain, (![A_252, B_253, C_254, D_255]: (k2_partfun1(u1_struct_0(A_252), u1_struct_0(B_253), C_254, u1_struct_0(D_255))=k2_tmap_1(A_252, B_253, C_254, D_255) | ~m1_pre_topc(D_255, A_252) | ~m1_subset_1(C_254, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_252), u1_struct_0(B_253)))) | ~v1_funct_2(C_254, u1_struct_0(A_252), u1_struct_0(B_253)) | ~v1_funct_1(C_254) | ~l1_pre_topc(B_253) | ~v2_pre_topc(B_253) | v2_struct_0(B_253) | ~l1_pre_topc(A_252) | ~v2_pre_topc(A_252) | v2_struct_0(A_252))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.76/2.01  tff(c_737, plain, (![D_255]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_6'), '#skF_7', u1_struct_0(D_255))=k2_tmap_1('#skF_3', '#skF_6', '#skF_7', D_255) | ~m1_pre_topc(D_255, '#skF_3') | ~v1_funct_2('#skF_7', u1_struct_0('#skF_3'), u1_struct_0('#skF_6')) | ~v1_funct_1('#skF_7') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_659, c_729])).
% 5.76/2.01  tff(c_749, plain, (![D_255]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_6'), '#skF_7', u1_struct_0(D_255))=k2_tmap_1('#skF_3', '#skF_6', '#skF_7', D_255) | ~m1_pre_topc(D_255, '#skF_3') | v2_struct_0('#skF_6') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_649, c_645, c_642, c_655, c_737])).
% 5.76/2.01  tff(c_750, plain, (![D_255]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_6'), '#skF_7', u1_struct_0(D_255))=k2_tmap_1('#skF_3', '#skF_6', '#skF_7', D_255) | ~m1_pre_topc(D_255, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_62, c_647, c_749])).
% 5.76/2.01  tff(c_959, plain, (k3_tmap_1('#skF_3', '#skF_6', '#skF_3', '#skF_4', '#skF_7')=k2_tmap_1('#skF_3', '#skF_6', '#skF_7', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_955, c_750])).
% 5.76/2.01  tff(c_966, plain, (k3_tmap_1('#skF_3', '#skF_6', '#skF_3', '#skF_4', '#skF_7')=k2_tmap_1('#skF_3', '#skF_6', '#skF_7', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_959])).
% 5.76/2.01  tff(c_80, plain, (v1_funct_2(k2_tmap_1('#skF_3', '#skF_6', '#skF_7', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_6')) | ~r1_tsep_1('#skF_4', '#skF_5') | ~r3_tsep_1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_215])).
% 5.76/2.01  tff(c_663, plain, (v1_funct_2(k2_tmap_1('#skF_3', '#skF_6', '#skF_7', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_643, c_260, c_80])).
% 5.76/2.01  tff(c_78, plain, (v5_pre_topc(k2_tmap_1('#skF_3', '#skF_6', '#skF_7', '#skF_4'), '#skF_4', '#skF_6') | ~r1_tsep_1('#skF_4', '#skF_5') | ~r3_tsep_1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_215])).
% 5.76/2.01  tff(c_661, plain, (v5_pre_topc(k2_tmap_1('#skF_3', '#skF_6', '#skF_7', '#skF_4'), '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_643, c_260, c_78])).
% 5.76/2.01  tff(c_76, plain, (m1_subset_1(k2_tmap_1('#skF_3', '#skF_6', '#skF_7', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_6')))) | ~r1_tsep_1('#skF_4', '#skF_5') | ~r3_tsep_1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_215])).
% 5.76/2.01  tff(c_667, plain, (m1_subset_1(k2_tmap_1('#skF_3', '#skF_6', '#skF_7', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_643, c_260, c_76])).
% 5.76/2.01  tff(c_74, plain, (v1_funct_1(k2_tmap_1('#skF_3', '#skF_6', '#skF_7', '#skF_5')) | ~r1_tsep_1('#skF_4', '#skF_5') | ~r3_tsep_1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_215])).
% 5.76/2.01  tff(c_651, plain, (v1_funct_1(k2_tmap_1('#skF_3', '#skF_6', '#skF_7', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_643, c_260, c_74])).
% 5.76/2.01  tff(c_861, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_6'), '#skF_7', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_3', '#skF_6', '#skF_3', '#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_837])).
% 5.76/2.01  tff(c_872, plain, (k3_tmap_1('#skF_3', '#skF_6', '#skF_3', '#skF_5', '#skF_7')=k2_tmap_1('#skF_3', '#skF_6', '#skF_7', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_861, c_750])).
% 5.76/2.01  tff(c_879, plain, (k3_tmap_1('#skF_3', '#skF_6', '#skF_3', '#skF_5', '#skF_7')=k2_tmap_1('#skF_3', '#skF_6', '#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_872])).
% 5.76/2.01  tff(c_72, plain, (v1_funct_2(k2_tmap_1('#skF_3', '#skF_6', '#skF_7', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_6')) | ~r1_tsep_1('#skF_4', '#skF_5') | ~r3_tsep_1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_215])).
% 5.76/2.01  tff(c_665, plain, (v1_funct_2(k2_tmap_1('#skF_3', '#skF_6', '#skF_7', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_643, c_260, c_72])).
% 5.76/2.01  tff(c_70, plain, (v5_pre_topc(k2_tmap_1('#skF_3', '#skF_6', '#skF_7', '#skF_5'), '#skF_5', '#skF_6') | ~r1_tsep_1('#skF_4', '#skF_5') | ~r3_tsep_1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_215])).
% 5.76/2.01  tff(c_657, plain, (v5_pre_topc(k2_tmap_1('#skF_3', '#skF_6', '#skF_7', '#skF_5'), '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_643, c_260, c_70])).
% 5.76/2.01  tff(c_68, plain, (m1_subset_1(k2_tmap_1('#skF_3', '#skF_6', '#skF_7', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_6')))) | ~r1_tsep_1('#skF_4', '#skF_5') | ~r3_tsep_1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_215])).
% 5.76/2.01  tff(c_669, plain, (m1_subset_1(k2_tmap_1('#skF_3', '#skF_6', '#skF_7', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_643, c_260, c_68])).
% 5.76/2.01  tff(c_1333, plain, (![A_315, D_317, E_319, C_316, B_318]: (v5_pre_topc(E_319, k1_tsep_1(A_315, B_318, C_316), D_317) | ~m1_subset_1(k3_tmap_1(A_315, D_317, k1_tsep_1(A_315, B_318, C_316), C_316, E_319), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_316), u1_struct_0(D_317)))) | ~v5_pre_topc(k3_tmap_1(A_315, D_317, k1_tsep_1(A_315, B_318, C_316), C_316, E_319), C_316, D_317) | ~v1_funct_2(k3_tmap_1(A_315, D_317, k1_tsep_1(A_315, B_318, C_316), C_316, E_319), u1_struct_0(C_316), u1_struct_0(D_317)) | ~v1_funct_1(k3_tmap_1(A_315, D_317, k1_tsep_1(A_315, B_318, C_316), C_316, E_319)) | ~m1_subset_1(k3_tmap_1(A_315, D_317, k1_tsep_1(A_315, B_318, C_316), B_318, E_319), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_318), u1_struct_0(D_317)))) | ~v5_pre_topc(k3_tmap_1(A_315, D_317, k1_tsep_1(A_315, B_318, C_316), B_318, E_319), B_318, D_317) | ~v1_funct_2(k3_tmap_1(A_315, D_317, k1_tsep_1(A_315, B_318, C_316), B_318, E_319), u1_struct_0(B_318), u1_struct_0(D_317)) | ~v1_funct_1(k3_tmap_1(A_315, D_317, k1_tsep_1(A_315, B_318, C_316), B_318, E_319)) | ~m1_subset_1(E_319, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_315, B_318, C_316)), u1_struct_0(D_317)))) | ~v1_funct_2(E_319, u1_struct_0(k1_tsep_1(A_315, B_318, C_316)), u1_struct_0(D_317)) | ~v1_funct_1(E_319) | ~l1_pre_topc(D_317) | ~v2_pre_topc(D_317) | v2_struct_0(D_317) | ~r3_tsep_1(A_315, B_318, C_316) | ~m1_pre_topc(C_316, A_315) | v2_struct_0(C_316) | ~m1_pre_topc(B_318, A_315) | v2_struct_0(B_318) | ~l1_pre_topc(A_315) | ~v2_pre_topc(A_315) | v2_struct_0(A_315))), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.76/2.01  tff(c_1343, plain, (![E_319, D_317]: (v5_pre_topc(E_319, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), D_317) | ~m1_subset_1(k3_tmap_1('#skF_3', D_317, '#skF_3', '#skF_5', E_319), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(D_317)))) | ~v5_pre_topc(k3_tmap_1('#skF_3', D_317, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', E_319), '#skF_5', D_317) | ~v1_funct_2(k3_tmap_1('#skF_3', D_317, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', E_319), u1_struct_0('#skF_5'), u1_struct_0(D_317)) | ~v1_funct_1(k3_tmap_1('#skF_3', D_317, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', E_319)) | ~m1_subset_1(k3_tmap_1('#skF_3', D_317, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', E_319), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(D_317)))) | ~v5_pre_topc(k3_tmap_1('#skF_3', D_317, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', E_319), '#skF_4', D_317) | ~v1_funct_2(k3_tmap_1('#skF_3', D_317, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', E_319), u1_struct_0('#skF_4'), u1_struct_0(D_317)) | ~v1_funct_1(k3_tmap_1('#skF_3', D_317, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', E_319)) | ~m1_subset_1(E_319, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0(D_317)))) | ~v1_funct_2(E_319, u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0(D_317)) | ~v1_funct_1(E_319) | ~l1_pre_topc(D_317) | ~v2_pre_topc(D_317) | v2_struct_0(D_317) | ~r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_1333])).
% 5.76/2.01  tff(c_1347, plain, (![E_319, D_317]: (v5_pre_topc(E_319, '#skF_3', D_317) | ~m1_subset_1(k3_tmap_1('#skF_3', D_317, '#skF_3', '#skF_5', E_319), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(D_317)))) | ~v5_pre_topc(k3_tmap_1('#skF_3', D_317, '#skF_3', '#skF_5', E_319), '#skF_5', D_317) | ~v1_funct_2(k3_tmap_1('#skF_3', D_317, '#skF_3', '#skF_5', E_319), u1_struct_0('#skF_5'), u1_struct_0(D_317)) | ~v1_funct_1(k3_tmap_1('#skF_3', D_317, '#skF_3', '#skF_5', E_319)) | ~m1_subset_1(k3_tmap_1('#skF_3', D_317, '#skF_3', '#skF_4', E_319), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(D_317)))) | ~v5_pre_topc(k3_tmap_1('#skF_3', D_317, '#skF_3', '#skF_4', E_319), '#skF_4', D_317) | ~v1_funct_2(k3_tmap_1('#skF_3', D_317, '#skF_3', '#skF_4', E_319), u1_struct_0('#skF_4'), u1_struct_0(D_317)) | ~v1_funct_1(k3_tmap_1('#skF_3', D_317, '#skF_3', '#skF_4', E_319)) | ~m1_subset_1(E_319, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(D_317)))) | ~v1_funct_2(E_319, u1_struct_0('#skF_3'), u1_struct_0(D_317)) | ~v1_funct_1(E_319) | ~l1_pre_topc(D_317) | ~v2_pre_topc(D_317) | v2_struct_0(D_317) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_50, c_643, c_48, c_48, c_48, c_48, c_48, c_48, c_48, c_48, c_48, c_48, c_1343])).
% 5.76/2.01  tff(c_1349, plain, (![E_320, D_321]: (v5_pre_topc(E_320, '#skF_3', D_321) | ~m1_subset_1(k3_tmap_1('#skF_3', D_321, '#skF_3', '#skF_5', E_320), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(D_321)))) | ~v5_pre_topc(k3_tmap_1('#skF_3', D_321, '#skF_3', '#skF_5', E_320), '#skF_5', D_321) | ~v1_funct_2(k3_tmap_1('#skF_3', D_321, '#skF_3', '#skF_5', E_320), u1_struct_0('#skF_5'), u1_struct_0(D_321)) | ~v1_funct_1(k3_tmap_1('#skF_3', D_321, '#skF_3', '#skF_5', E_320)) | ~m1_subset_1(k3_tmap_1('#skF_3', D_321, '#skF_3', '#skF_4', E_320), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(D_321)))) | ~v5_pre_topc(k3_tmap_1('#skF_3', D_321, '#skF_3', '#skF_4', E_320), '#skF_4', D_321) | ~v1_funct_2(k3_tmap_1('#skF_3', D_321, '#skF_3', '#skF_4', E_320), u1_struct_0('#skF_4'), u1_struct_0(D_321)) | ~v1_funct_1(k3_tmap_1('#skF_3', D_321, '#skF_3', '#skF_4', E_320)) | ~m1_subset_1(E_320, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(D_321)))) | ~v1_funct_2(E_320, u1_struct_0('#skF_3'), u1_struct_0(D_321)) | ~v1_funct_1(E_320) | ~l1_pre_topc(D_321) | ~v2_pre_topc(D_321) | v2_struct_0(D_321))), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_52, c_1347])).
% 5.76/2.01  tff(c_1352, plain, (v5_pre_topc('#skF_7', '#skF_3', '#skF_6') | ~m1_subset_1(k2_tmap_1('#skF_3', '#skF_6', '#skF_7', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_6')))) | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_6', '#skF_3', '#skF_5', '#skF_7'), '#skF_5', '#skF_6') | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_6', '#skF_3', '#skF_5', '#skF_7'), u1_struct_0('#skF_5'), u1_struct_0('#skF_6')) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_6', '#skF_3', '#skF_5', '#skF_7')) | ~m1_subset_1(k3_tmap_1('#skF_3', '#skF_6', '#skF_3', '#skF_4', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_6')))) | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_6', '#skF_3', '#skF_4', '#skF_7'), '#skF_4', '#skF_6') | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_6', '#skF_3', '#skF_4', '#skF_7'), u1_struct_0('#skF_4'), u1_struct_0('#skF_6')) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_6', '#skF_3', '#skF_4', '#skF_7')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_6')))) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_3'), u1_struct_0('#skF_6')) | ~v1_funct_1('#skF_7') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_879, c_1349])).
% 5.76/2.01  tff(c_1354, plain, (v5_pre_topc('#skF_7', '#skF_3', '#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_649, c_645, c_642, c_655, c_659, c_653, c_966, c_663, c_966, c_661, c_966, c_667, c_966, c_651, c_879, c_665, c_879, c_657, c_879, c_669, c_1352])).
% 5.76/2.01  tff(c_1356, plain, $false, inference(negUnitSimplification, [status(thm)], [c_647, c_679, c_1354])).
% 5.76/2.01  tff(c_1358, plain, (~r1_tsep_1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_224])).
% 5.76/2.01  tff(c_1357, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_224])).
% 5.76/2.01  tff(c_1387, plain, (![B_322, C_323, A_324]: (r1_tsep_1(B_322, C_323) | ~r3_tsep_1(A_324, B_322, C_323) | ~m1_pre_topc(C_323, A_324) | v2_struct_0(C_323) | ~m1_pre_topc(B_322, A_324) | v2_struct_0(B_322) | ~l1_pre_topc(A_324) | ~v2_pre_topc(A_324) | v2_struct_0(A_324))), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.76/2.01  tff(c_1390, plain, (r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1357, c_1387])).
% 5.76/2.01  tff(c_1393, plain, (r1_tsep_1('#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_50, c_1390])).
% 5.76/2.01  tff(c_1395, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_52, c_1358, c_1393])).
% 5.76/2.01  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.76/2.01  
% 5.76/2.01  Inference rules
% 5.76/2.01  ----------------------
% 5.76/2.01  #Ref     : 0
% 5.76/2.01  #Sup     : 202
% 5.76/2.01  #Fact    : 0
% 5.76/2.01  #Define  : 0
% 5.76/2.01  #Split   : 10
% 5.76/2.01  #Chain   : 0
% 5.76/2.01  #Close   : 0
% 5.76/2.01  
% 5.76/2.01  Ordering : KBO
% 5.76/2.01  
% 5.76/2.01  Simplification rules
% 5.76/2.01  ----------------------
% 5.76/2.01  #Subsume      : 74
% 5.76/2.01  #Demod        : 557
% 5.76/2.01  #Tautology    : 157
% 5.76/2.01  #SimpNegUnit  : 75
% 5.76/2.01  #BackRed      : 3
% 5.76/2.01  
% 5.76/2.01  #Partial instantiations: 0
% 5.76/2.01  #Strategies tried      : 1
% 5.76/2.01  
% 5.76/2.01  Timing (in seconds)
% 5.76/2.01  ----------------------
% 5.76/2.02  Preprocessing        : 0.46
% 5.76/2.02  Parsing              : 0.19
% 5.76/2.02  CNF conversion       : 0.06
% 5.76/2.02  Main loop            : 0.73
% 5.76/2.02  Inferencing          : 0.24
% 5.76/2.02  Reduction            : 0.25
% 5.76/2.02  Demodulation         : 0.18
% 5.76/2.02  BG Simplification    : 0.07
% 5.76/2.02  Subsumption          : 0.16
% 5.76/2.02  Abstraction          : 0.05
% 5.76/2.02  MUC search           : 0.00
% 5.76/2.02  Cooper               : 0.00
% 5.76/2.02  Total                : 1.26
% 5.76/2.02  Index Insertion      : 0.00
% 5.76/2.02  Index Deletion       : 0.00
% 5.76/2.02  Index Matching       : 0.00
% 5.76/2.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
