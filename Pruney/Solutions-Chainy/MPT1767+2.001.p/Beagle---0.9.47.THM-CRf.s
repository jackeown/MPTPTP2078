%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:15 EST 2020

% Result     : Theorem 3.57s
% Output     : CNFRefutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 914 expanded)
%              Number of leaves         :   31 ( 377 expanded)
%              Depth                    :   21
%              Number of atoms          :  377 (6867 expanded)
%              Number of equality atoms :   18 ( 178 expanded)
%              Maximal formula depth    :   26 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_224,negated_conjecture,(
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
                          & v1_funct_2(E,u1_struct_0(A),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                       => ( m1_pre_topc(C,D)
                         => r2_funct_2(u1_struct_0(C),u1_struct_0(B),k3_tmap_1(A,B,D,C,k2_tmap_1(A,B,E,D)),k2_tmap_1(A,B,E,C)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tmap_1)).

tff(f_138,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_134,axiom,(
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

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,A,B)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( r2_funct_2(A,B,C,D)
          <=> ! [E] :
                ( m1_subset_1(E,A)
               => k1_funct_1(C,E) = k1_funct_1(D,E) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_2)).

tff(f_185,axiom,(
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
                     => ! [F] :
                          ( ( v1_funct_1(F)
                            & v1_funct_2(F,u1_struct_0(C),u1_struct_0(B))
                            & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                         => ( ( r2_funct_2(u1_struct_0(C),u1_struct_0(B),F,k2_tmap_1(A,B,E,C))
                              & m1_pre_topc(D,C) )
                           => r2_funct_2(u1_struct_0(D),u1_struct_0(B),k3_tmap_1(A,B,C,D,F),k2_tmap_1(A,B,E,D)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tmap_1)).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_36,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_24,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_48,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_46,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_42,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_40,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_32,plain,(
    m1_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_30,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_28,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_26,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_18,plain,(
    ! [A_64] :
      ( m1_pre_topc(A_64,A_64)
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_135,plain,(
    ! [D_207,B_206,C_205,A_204,E_203] :
      ( k3_tmap_1(A_204,B_206,C_205,D_207,E_203) = k2_partfun1(u1_struct_0(C_205),u1_struct_0(B_206),E_203,u1_struct_0(D_207))
      | ~ m1_pre_topc(D_207,C_205)
      | ~ m1_subset_1(E_203,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_205),u1_struct_0(B_206))))
      | ~ v1_funct_2(E_203,u1_struct_0(C_205),u1_struct_0(B_206))
      | ~ v1_funct_1(E_203)
      | ~ m1_pre_topc(D_207,A_204)
      | ~ m1_pre_topc(C_205,A_204)
      | ~ l1_pre_topc(B_206)
      | ~ v2_pre_topc(B_206)
      | v2_struct_0(B_206)
      | ~ l1_pre_topc(A_204)
      | ~ v2_pre_topc(A_204)
      | v2_struct_0(A_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_139,plain,(
    ! [A_204,D_207] :
      ( k3_tmap_1(A_204,'#skF_3','#skF_2',D_207,'#skF_6') = k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_207))
      | ~ m1_pre_topc(D_207,'#skF_2')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_207,A_204)
      | ~ m1_pre_topc('#skF_2',A_204)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_204)
      | ~ v2_pre_topc(A_204)
      | v2_struct_0(A_204) ) ),
    inference(resolution,[status(thm)],[c_26,c_135])).

tff(c_143,plain,(
    ! [A_204,D_207] :
      ( k3_tmap_1(A_204,'#skF_3','#skF_2',D_207,'#skF_6') = k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_207))
      | ~ m1_pre_topc(D_207,'#skF_2')
      | ~ m1_pre_topc(D_207,A_204)
      | ~ m1_pre_topc('#skF_2',A_204)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_204)
      | ~ v2_pre_topc(A_204)
      | v2_struct_0(A_204) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_30,c_28,c_139])).

tff(c_145,plain,(
    ! [A_208,D_209] :
      ( k3_tmap_1(A_208,'#skF_3','#skF_2',D_209,'#skF_6') = k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_209))
      | ~ m1_pre_topc(D_209,'#skF_2')
      | ~ m1_pre_topc(D_209,A_208)
      | ~ m1_pre_topc('#skF_2',A_208)
      | ~ l1_pre_topc(A_208)
      | ~ v2_pre_topc(A_208)
      | v2_struct_0(A_208) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_143])).

tff(c_151,plain,
    ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_5','#skF_6')
    | ~ m1_pre_topc('#skF_5','#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_145])).

tff(c_161,plain,
    ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_5','#skF_6')
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_32,c_151])).

tff(c_162,plain,
    ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_5','#skF_6')
    | ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_161])).

tff(c_167,plain,(
    ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_162])).

tff(c_170,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_167])).

tff(c_174,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_170])).

tff(c_176,plain,(
    m1_pre_topc('#skF_2','#skF_2') ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_175,plain,(
    k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_85,plain,(
    ! [A_182,B_183,C_184,D_185] :
      ( k2_partfun1(u1_struct_0(A_182),u1_struct_0(B_183),C_184,u1_struct_0(D_185)) = k2_tmap_1(A_182,B_183,C_184,D_185)
      | ~ m1_pre_topc(D_185,A_182)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_182),u1_struct_0(B_183))))
      | ~ v1_funct_2(C_184,u1_struct_0(A_182),u1_struct_0(B_183))
      | ~ v1_funct_1(C_184)
      | ~ l1_pre_topc(B_183)
      | ~ v2_pre_topc(B_183)
      | v2_struct_0(B_183)
      | ~ l1_pre_topc(A_182)
      | ~ v2_pre_topc(A_182)
      | v2_struct_0(A_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_87,plain,(
    ! [D_185] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_185)) = k2_tmap_1('#skF_2','#skF_3','#skF_6',D_185)
      | ~ m1_pre_topc(D_185,'#skF_2')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_85])).

tff(c_90,plain,(
    ! [D_185] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_185)) = k2_tmap_1('#skF_2','#skF_3','#skF_6',D_185)
      | ~ m1_pre_topc(D_185,'#skF_2')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_42,c_40,c_30,c_28,c_87])).

tff(c_91,plain,(
    ! [D_185] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_185)) = k2_tmap_1('#skF_2','#skF_3','#skF_6',D_185)
      | ~ m1_pre_topc(D_185,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_44,c_90])).

tff(c_187,plain,
    ( k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_5','#skF_6') = k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_91])).

tff(c_194,plain,(
    k3_tmap_1('#skF_2','#skF_3','#skF_2','#skF_5','#skF_6') = k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_187])).

tff(c_67,plain,(
    ! [D_171,A_169,C_168,B_170,E_172] :
      ( v1_funct_1(k3_tmap_1(A_169,B_170,C_168,D_171,E_172))
      | ~ m1_subset_1(E_172,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_168),u1_struct_0(B_170))))
      | ~ v1_funct_2(E_172,u1_struct_0(C_168),u1_struct_0(B_170))
      | ~ v1_funct_1(E_172)
      | ~ m1_pre_topc(D_171,A_169)
      | ~ m1_pre_topc(C_168,A_169)
      | ~ l1_pre_topc(B_170)
      | ~ v2_pre_topc(B_170)
      | v2_struct_0(B_170)
      | ~ l1_pre_topc(A_169)
      | ~ v2_pre_topc(A_169)
      | v2_struct_0(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_69,plain,(
    ! [A_169,D_171] :
      ( v1_funct_1(k3_tmap_1(A_169,'#skF_3','#skF_2',D_171,'#skF_6'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_171,A_169)
      | ~ m1_pre_topc('#skF_2',A_169)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_169)
      | ~ v2_pre_topc(A_169)
      | v2_struct_0(A_169) ) ),
    inference(resolution,[status(thm)],[c_26,c_67])).

tff(c_72,plain,(
    ! [A_169,D_171] :
      ( v1_funct_1(k3_tmap_1(A_169,'#skF_3','#skF_2',D_171,'#skF_6'))
      | ~ m1_pre_topc(D_171,A_169)
      | ~ m1_pre_topc('#skF_2',A_169)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_169)
      | ~ v2_pre_topc(A_169)
      | v2_struct_0(A_169) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_30,c_28,c_69])).

tff(c_73,plain,(
    ! [A_169,D_171] :
      ( v1_funct_1(k3_tmap_1(A_169,'#skF_3','#skF_2',D_171,'#skF_6'))
      | ~ m1_pre_topc(D_171,A_169)
      | ~ m1_pre_topc('#skF_2',A_169)
      | ~ l1_pre_topc(A_169)
      | ~ v2_pre_topc(A_169)
      | v2_struct_0(A_169) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_72])).

tff(c_208,plain,
    ( v1_funct_1(k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_5'))
    | ~ m1_pre_topc('#skF_5','#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_73])).

tff(c_218,plain,
    ( v1_funct_1(k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_5'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_176,c_32,c_208])).

tff(c_219,plain,(
    v1_funct_1(k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_218])).

tff(c_101,plain,(
    ! [C_187,E_191,B_189,A_188,D_190] :
      ( v1_funct_2(k3_tmap_1(A_188,B_189,C_187,D_190,E_191),u1_struct_0(D_190),u1_struct_0(B_189))
      | ~ m1_subset_1(E_191,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_187),u1_struct_0(B_189))))
      | ~ v1_funct_2(E_191,u1_struct_0(C_187),u1_struct_0(B_189))
      | ~ v1_funct_1(E_191)
      | ~ m1_pre_topc(D_190,A_188)
      | ~ m1_pre_topc(C_187,A_188)
      | ~ l1_pre_topc(B_189)
      | ~ v2_pre_topc(B_189)
      | v2_struct_0(B_189)
      | ~ l1_pre_topc(A_188)
      | ~ v2_pre_topc(A_188)
      | v2_struct_0(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_103,plain,(
    ! [A_188,D_190] :
      ( v1_funct_2(k3_tmap_1(A_188,'#skF_3','#skF_2',D_190,'#skF_6'),u1_struct_0(D_190),u1_struct_0('#skF_3'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_190,A_188)
      | ~ m1_pre_topc('#skF_2',A_188)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_188)
      | ~ v2_pre_topc(A_188)
      | v2_struct_0(A_188) ) ),
    inference(resolution,[status(thm)],[c_26,c_101])).

tff(c_106,plain,(
    ! [A_188,D_190] :
      ( v1_funct_2(k3_tmap_1(A_188,'#skF_3','#skF_2',D_190,'#skF_6'),u1_struct_0(D_190),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(D_190,A_188)
      | ~ m1_pre_topc('#skF_2',A_188)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_188)
      | ~ v2_pre_topc(A_188)
      | v2_struct_0(A_188) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_30,c_28,c_103])).

tff(c_107,plain,(
    ! [A_188,D_190] :
      ( v1_funct_2(k3_tmap_1(A_188,'#skF_3','#skF_2',D_190,'#skF_6'),u1_struct_0(D_190),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(D_190,A_188)
      | ~ m1_pre_topc('#skF_2',A_188)
      | ~ l1_pre_topc(A_188)
      | ~ v2_pre_topc(A_188)
      | v2_struct_0(A_188) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_106])).

tff(c_205,plain,
    ( v1_funct_2(k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_5','#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_107])).

tff(c_215,plain,
    ( v1_funct_2(k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_176,c_32,c_205])).

tff(c_216,plain,(
    v1_funct_2(k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_215])).

tff(c_12,plain,(
    ! [D_62,A_59,C_61,E_63,B_60] :
      ( m1_subset_1(k3_tmap_1(A_59,B_60,C_61,D_62,E_63),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_62),u1_struct_0(B_60))))
      | ~ m1_subset_1(E_63,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_61),u1_struct_0(B_60))))
      | ~ v1_funct_2(E_63,u1_struct_0(C_61),u1_struct_0(B_60))
      | ~ v1_funct_1(E_63)
      | ~ m1_pre_topc(D_62,A_59)
      | ~ m1_pre_topc(C_61,A_59)
      | ~ l1_pre_topc(B_60)
      | ~ v2_pre_topc(B_60)
      | v2_struct_0(B_60)
      | ~ l1_pre_topc(A_59)
      | ~ v2_pre_topc(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_202,plain,
    ( m1_subset_1(k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_pre_topc('#skF_5','#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_12])).

tff(c_212,plain,
    ( m1_subset_1(k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_42,c_40,c_176,c_32,c_30,c_28,c_26,c_202])).

tff(c_213,plain,(
    m1_subset_1(k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3')))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_44,c_212])).

tff(c_4,plain,(
    ! [D_9,A_1,B_2,C_3] :
      ( k1_funct_1(D_9,'#skF_1'(A_1,B_2,C_3,D_9)) != k1_funct_1(C_3,'#skF_1'(A_1,B_2,C_3,D_9))
      | r2_funct_2(A_1,B_2,C_3,D_9)
      | ~ m1_subset_1(D_9,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ v1_funct_2(D_9,A_1,B_2)
      | ~ v1_funct_1(D_9)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ v1_funct_2(C_3,A_1,B_2)
      | ~ v1_funct_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_77,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_funct_2(A_1,B_2,C_3,C_3)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ v1_funct_2(C_3,A_1,B_2)
      | ~ v1_funct_1(C_3)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ v1_funct_2(C_3,A_1,B_2)
      | ~ v1_funct_1(C_3) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_4])).

tff(c_229,plain,
    ( r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_5'),k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_5'))
    | ~ m1_subset_1(k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_5')) ),
    inference(resolution,[status(thm)],[c_213,c_77])).

tff(c_250,plain,(
    r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_5'),k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_216,c_213,c_229])).

tff(c_20,plain,(
    ! [A_65,F_127,D_121,E_125,B_97,C_113] :
      ( r2_funct_2(u1_struct_0(D_121),u1_struct_0(B_97),k3_tmap_1(A_65,B_97,C_113,D_121,F_127),k2_tmap_1(A_65,B_97,E_125,D_121))
      | ~ m1_pre_topc(D_121,C_113)
      | ~ r2_funct_2(u1_struct_0(C_113),u1_struct_0(B_97),F_127,k2_tmap_1(A_65,B_97,E_125,C_113))
      | ~ m1_subset_1(F_127,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_113),u1_struct_0(B_97))))
      | ~ v1_funct_2(F_127,u1_struct_0(C_113),u1_struct_0(B_97))
      | ~ v1_funct_1(F_127)
      | ~ m1_subset_1(E_125,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_65),u1_struct_0(B_97))))
      | ~ v1_funct_2(E_125,u1_struct_0(A_65),u1_struct_0(B_97))
      | ~ v1_funct_1(E_125)
      | ~ m1_pre_topc(D_121,A_65)
      | v2_struct_0(D_121)
      | ~ m1_pre_topc(C_113,A_65)
      | v2_struct_0(C_113)
      | ~ l1_pre_topc(B_97)
      | ~ v2_pre_topc(B_97)
      | v2_struct_0(B_97)
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65)
      | v2_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_384,plain,(
    ! [D_121] :
      ( r2_funct_2(u1_struct_0(D_121),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_5',D_121,k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_5')),k2_tmap_1('#skF_2','#skF_3','#skF_6',D_121))
      | ~ m1_pre_topc(D_121,'#skF_5')
      | ~ m1_subset_1(k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_5'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_121,'#skF_2')
      | v2_struct_0(D_121)
      | ~ m1_pre_topc('#skF_5','#skF_2')
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_250,c_20])).

tff(c_387,plain,(
    ! [D_121] :
      ( r2_funct_2(u1_struct_0(D_121),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_5',D_121,k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_5')),k2_tmap_1('#skF_2','#skF_3','#skF_6',D_121))
      | ~ m1_pre_topc(D_121,'#skF_5')
      | ~ m1_pre_topc(D_121,'#skF_2')
      | v2_struct_0(D_121)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_42,c_40,c_32,c_30,c_28,c_26,c_219,c_216,c_213,c_384])).

tff(c_769,plain,(
    ! [D_265] :
      ( r2_funct_2(u1_struct_0(D_265),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_5',D_265,k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_5')),k2_tmap_1('#skF_2','#skF_3','#skF_6',D_265))
      | ~ m1_pre_topc(D_265,'#skF_5')
      | ~ m1_pre_topc(D_265,'#skF_2')
      | v2_struct_0(D_265) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_44,c_34,c_387])).

tff(c_22,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4',k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_5')),k2_tmap_1('#skF_2','#skF_3','#skF_6','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_777,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_769,c_22])).

tff(c_788,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_24,c_777])).

tff(c_790,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_788])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:28:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.57/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.57/1.61  
% 3.57/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.57/1.61  %$ r2_funct_2 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.57/1.61  
% 3.57/1.61  %Foreground sorts:
% 3.57/1.61  
% 3.57/1.61  
% 3.57/1.61  %Background operators:
% 3.57/1.61  
% 3.57/1.61  
% 3.57/1.61  %Foreground operators:
% 3.57/1.61  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.57/1.61  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.57/1.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.57/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.57/1.61  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.57/1.61  tff('#skF_5', type, '#skF_5': $i).
% 3.57/1.61  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.57/1.61  tff('#skF_6', type, '#skF_6': $i).
% 3.57/1.61  tff('#skF_2', type, '#skF_2': $i).
% 3.57/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.57/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.57/1.61  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.57/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.57/1.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.57/1.61  tff('#skF_4', type, '#skF_4': $i).
% 3.57/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.57/1.61  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.57/1.61  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.57/1.61  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.57/1.61  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.57/1.61  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.57/1.61  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.57/1.61  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 3.57/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.57/1.61  
% 3.57/1.63  tff(f_224, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (m1_pre_topc(C, D) => r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, D, C, k2_tmap_1(A, B, E, D)), k2_tmap_1(A, B, E, C))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_tmap_1)).
% 3.57/1.63  tff(f_138, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 3.57/1.63  tff(f_104, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 3.57/1.63  tff(f_72, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 3.57/1.63  tff(f_134, axiom, (![A, B, C, D, E]: (((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & m1_pre_topc(C, A)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((v1_funct_1(k3_tmap_1(A, B, C, D, E)) & v1_funct_2(k3_tmap_1(A, B, C, D, E), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k3_tmap_1(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 3.57/1.63  tff(f_45, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (![E]: (m1_subset_1(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_2)).
% 3.57/1.63  tff(f_185, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((r2_funct_2(u1_struct_0(C), u1_struct_0(B), F, k2_tmap_1(A, B, E, C)) & m1_pre_topc(D, C)) => r2_funct_2(u1_struct_0(D), u1_struct_0(B), k3_tmap_1(A, B, C, D, F), k2_tmap_1(A, B, E, D))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tmap_1)).
% 3.57/1.63  tff(c_38, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_224])).
% 3.57/1.63  tff(c_36, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_224])).
% 3.57/1.63  tff(c_24, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_224])).
% 3.57/1.63  tff(c_50, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_224])).
% 3.57/1.63  tff(c_44, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_224])).
% 3.57/1.63  tff(c_34, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_224])).
% 3.57/1.63  tff(c_48, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_224])).
% 3.57/1.63  tff(c_46, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_224])).
% 3.57/1.63  tff(c_42, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_224])).
% 3.57/1.63  tff(c_40, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_224])).
% 3.57/1.63  tff(c_32, plain, (m1_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_224])).
% 3.57/1.63  tff(c_30, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_224])).
% 3.57/1.63  tff(c_28, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_224])).
% 3.57/1.63  tff(c_26, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_224])).
% 3.57/1.63  tff(c_18, plain, (![A_64]: (m1_pre_topc(A_64, A_64) | ~l1_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.57/1.63  tff(c_135, plain, (![D_207, B_206, C_205, A_204, E_203]: (k3_tmap_1(A_204, B_206, C_205, D_207, E_203)=k2_partfun1(u1_struct_0(C_205), u1_struct_0(B_206), E_203, u1_struct_0(D_207)) | ~m1_pre_topc(D_207, C_205) | ~m1_subset_1(E_203, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_205), u1_struct_0(B_206)))) | ~v1_funct_2(E_203, u1_struct_0(C_205), u1_struct_0(B_206)) | ~v1_funct_1(E_203) | ~m1_pre_topc(D_207, A_204) | ~m1_pre_topc(C_205, A_204) | ~l1_pre_topc(B_206) | ~v2_pre_topc(B_206) | v2_struct_0(B_206) | ~l1_pre_topc(A_204) | ~v2_pre_topc(A_204) | v2_struct_0(A_204))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.57/1.63  tff(c_139, plain, (![A_204, D_207]: (k3_tmap_1(A_204, '#skF_3', '#skF_2', D_207, '#skF_6')=k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_207)) | ~m1_pre_topc(D_207, '#skF_2') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_207, A_204) | ~m1_pre_topc('#skF_2', A_204) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_204) | ~v2_pre_topc(A_204) | v2_struct_0(A_204))), inference(resolution, [status(thm)], [c_26, c_135])).
% 3.57/1.63  tff(c_143, plain, (![A_204, D_207]: (k3_tmap_1(A_204, '#skF_3', '#skF_2', D_207, '#skF_6')=k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_207)) | ~m1_pre_topc(D_207, '#skF_2') | ~m1_pre_topc(D_207, A_204) | ~m1_pre_topc('#skF_2', A_204) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_204) | ~v2_pre_topc(A_204) | v2_struct_0(A_204))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_30, c_28, c_139])).
% 3.57/1.63  tff(c_145, plain, (![A_208, D_209]: (k3_tmap_1(A_208, '#skF_3', '#skF_2', D_209, '#skF_6')=k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_209)) | ~m1_pre_topc(D_209, '#skF_2') | ~m1_pre_topc(D_209, A_208) | ~m1_pre_topc('#skF_2', A_208) | ~l1_pre_topc(A_208) | ~v2_pre_topc(A_208) | v2_struct_0(A_208))), inference(negUnitSimplification, [status(thm)], [c_44, c_143])).
% 3.57/1.63  tff(c_151, plain, (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_5', '#skF_6') | ~m1_pre_topc('#skF_5', '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_32, c_145])).
% 3.57/1.63  tff(c_161, plain, (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_5', '#skF_6') | ~m1_pre_topc('#skF_2', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_32, c_151])).
% 3.57/1.63  tff(c_162, plain, (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_5', '#skF_6') | ~m1_pre_topc('#skF_2', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_50, c_161])).
% 3.57/1.63  tff(c_167, plain, (~m1_pre_topc('#skF_2', '#skF_2')), inference(splitLeft, [status(thm)], [c_162])).
% 3.57/1.63  tff(c_170, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_18, c_167])).
% 3.57/1.63  tff(c_174, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_170])).
% 3.57/1.63  tff(c_176, plain, (m1_pre_topc('#skF_2', '#skF_2')), inference(splitRight, [status(thm)], [c_162])).
% 3.57/1.63  tff(c_175, plain, (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_162])).
% 3.57/1.63  tff(c_85, plain, (![A_182, B_183, C_184, D_185]: (k2_partfun1(u1_struct_0(A_182), u1_struct_0(B_183), C_184, u1_struct_0(D_185))=k2_tmap_1(A_182, B_183, C_184, D_185) | ~m1_pre_topc(D_185, A_182) | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_182), u1_struct_0(B_183)))) | ~v1_funct_2(C_184, u1_struct_0(A_182), u1_struct_0(B_183)) | ~v1_funct_1(C_184) | ~l1_pre_topc(B_183) | ~v2_pre_topc(B_183) | v2_struct_0(B_183) | ~l1_pre_topc(A_182) | ~v2_pre_topc(A_182) | v2_struct_0(A_182))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.57/1.63  tff(c_87, plain, (![D_185]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_185))=k2_tmap_1('#skF_2', '#skF_3', '#skF_6', D_185) | ~m1_pre_topc(D_185, '#skF_2') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_26, c_85])).
% 3.57/1.63  tff(c_90, plain, (![D_185]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_185))=k2_tmap_1('#skF_2', '#skF_3', '#skF_6', D_185) | ~m1_pre_topc(D_185, '#skF_2') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_42, c_40, c_30, c_28, c_87])).
% 3.57/1.63  tff(c_91, plain, (![D_185]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_185))=k2_tmap_1('#skF_2', '#skF_3', '#skF_6', D_185) | ~m1_pre_topc(D_185, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_50, c_44, c_90])).
% 3.57/1.63  tff(c_187, plain, (k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_5', '#skF_6')=k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_175, c_91])).
% 3.57/1.63  tff(c_194, plain, (k3_tmap_1('#skF_2', '#skF_3', '#skF_2', '#skF_5', '#skF_6')=k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_187])).
% 3.57/1.63  tff(c_67, plain, (![D_171, A_169, C_168, B_170, E_172]: (v1_funct_1(k3_tmap_1(A_169, B_170, C_168, D_171, E_172)) | ~m1_subset_1(E_172, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_168), u1_struct_0(B_170)))) | ~v1_funct_2(E_172, u1_struct_0(C_168), u1_struct_0(B_170)) | ~v1_funct_1(E_172) | ~m1_pre_topc(D_171, A_169) | ~m1_pre_topc(C_168, A_169) | ~l1_pre_topc(B_170) | ~v2_pre_topc(B_170) | v2_struct_0(B_170) | ~l1_pre_topc(A_169) | ~v2_pre_topc(A_169) | v2_struct_0(A_169))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.57/1.63  tff(c_69, plain, (![A_169, D_171]: (v1_funct_1(k3_tmap_1(A_169, '#skF_3', '#skF_2', D_171, '#skF_6')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_171, A_169) | ~m1_pre_topc('#skF_2', A_169) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_169) | ~v2_pre_topc(A_169) | v2_struct_0(A_169))), inference(resolution, [status(thm)], [c_26, c_67])).
% 3.57/1.63  tff(c_72, plain, (![A_169, D_171]: (v1_funct_1(k3_tmap_1(A_169, '#skF_3', '#skF_2', D_171, '#skF_6')) | ~m1_pre_topc(D_171, A_169) | ~m1_pre_topc('#skF_2', A_169) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_169) | ~v2_pre_topc(A_169) | v2_struct_0(A_169))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_30, c_28, c_69])).
% 3.57/1.63  tff(c_73, plain, (![A_169, D_171]: (v1_funct_1(k3_tmap_1(A_169, '#skF_3', '#skF_2', D_171, '#skF_6')) | ~m1_pre_topc(D_171, A_169) | ~m1_pre_topc('#skF_2', A_169) | ~l1_pre_topc(A_169) | ~v2_pre_topc(A_169) | v2_struct_0(A_169))), inference(negUnitSimplification, [status(thm)], [c_44, c_72])).
% 3.57/1.63  tff(c_208, plain, (v1_funct_1(k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_5')) | ~m1_pre_topc('#skF_5', '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_194, c_73])).
% 3.57/1.63  tff(c_218, plain, (v1_funct_1(k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_5')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_176, c_32, c_208])).
% 3.57/1.63  tff(c_219, plain, (v1_funct_1(k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_50, c_218])).
% 3.57/1.63  tff(c_101, plain, (![C_187, E_191, B_189, A_188, D_190]: (v1_funct_2(k3_tmap_1(A_188, B_189, C_187, D_190, E_191), u1_struct_0(D_190), u1_struct_0(B_189)) | ~m1_subset_1(E_191, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_187), u1_struct_0(B_189)))) | ~v1_funct_2(E_191, u1_struct_0(C_187), u1_struct_0(B_189)) | ~v1_funct_1(E_191) | ~m1_pre_topc(D_190, A_188) | ~m1_pre_topc(C_187, A_188) | ~l1_pre_topc(B_189) | ~v2_pre_topc(B_189) | v2_struct_0(B_189) | ~l1_pre_topc(A_188) | ~v2_pre_topc(A_188) | v2_struct_0(A_188))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.57/1.63  tff(c_103, plain, (![A_188, D_190]: (v1_funct_2(k3_tmap_1(A_188, '#skF_3', '#skF_2', D_190, '#skF_6'), u1_struct_0(D_190), u1_struct_0('#skF_3')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_190, A_188) | ~m1_pre_topc('#skF_2', A_188) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_188) | ~v2_pre_topc(A_188) | v2_struct_0(A_188))), inference(resolution, [status(thm)], [c_26, c_101])).
% 3.57/1.63  tff(c_106, plain, (![A_188, D_190]: (v1_funct_2(k3_tmap_1(A_188, '#skF_3', '#skF_2', D_190, '#skF_6'), u1_struct_0(D_190), u1_struct_0('#skF_3')) | ~m1_pre_topc(D_190, A_188) | ~m1_pre_topc('#skF_2', A_188) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_188) | ~v2_pre_topc(A_188) | v2_struct_0(A_188))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_30, c_28, c_103])).
% 3.57/1.63  tff(c_107, plain, (![A_188, D_190]: (v1_funct_2(k3_tmap_1(A_188, '#skF_3', '#skF_2', D_190, '#skF_6'), u1_struct_0(D_190), u1_struct_0('#skF_3')) | ~m1_pre_topc(D_190, A_188) | ~m1_pre_topc('#skF_2', A_188) | ~l1_pre_topc(A_188) | ~v2_pre_topc(A_188) | v2_struct_0(A_188))), inference(negUnitSimplification, [status(thm)], [c_44, c_106])).
% 3.57/1.63  tff(c_205, plain, (v1_funct_2(k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_5', '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_194, c_107])).
% 3.57/1.63  tff(c_215, plain, (v1_funct_2(k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_176, c_32, c_205])).
% 3.57/1.63  tff(c_216, plain, (v1_funct_2(k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_50, c_215])).
% 3.57/1.63  tff(c_12, plain, (![D_62, A_59, C_61, E_63, B_60]: (m1_subset_1(k3_tmap_1(A_59, B_60, C_61, D_62, E_63), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_62), u1_struct_0(B_60)))) | ~m1_subset_1(E_63, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_61), u1_struct_0(B_60)))) | ~v1_funct_2(E_63, u1_struct_0(C_61), u1_struct_0(B_60)) | ~v1_funct_1(E_63) | ~m1_pre_topc(D_62, A_59) | ~m1_pre_topc(C_61, A_59) | ~l1_pre_topc(B_60) | ~v2_pre_topc(B_60) | v2_struct_0(B_60) | ~l1_pre_topc(A_59) | ~v2_pre_topc(A_59) | v2_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.57/1.63  tff(c_202, plain, (m1_subset_1(k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3')))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_194, c_12])).
% 3.57/1.63  tff(c_212, plain, (m1_subset_1(k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3')))) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_42, c_40, c_176, c_32, c_30, c_28, c_26, c_202])).
% 3.57/1.63  tff(c_213, plain, (m1_subset_1(k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_44, c_212])).
% 3.57/1.63  tff(c_4, plain, (![D_9, A_1, B_2, C_3]: (k1_funct_1(D_9, '#skF_1'(A_1, B_2, C_3, D_9))!=k1_funct_1(C_3, '#skF_1'(A_1, B_2, C_3, D_9)) | r2_funct_2(A_1, B_2, C_3, D_9) | ~m1_subset_1(D_9, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(D_9, A_1, B_2) | ~v1_funct_1(D_9) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(C_3, A_1, B_2) | ~v1_funct_1(C_3))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.57/1.63  tff(c_77, plain, (![A_1, B_2, C_3]: (r2_funct_2(A_1, B_2, C_3, C_3) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(C_3, A_1, B_2) | ~v1_funct_1(C_3) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(C_3, A_1, B_2) | ~v1_funct_1(C_3))), inference(reflexivity, [status(thm), theory('equality')], [c_4])).
% 3.57/1.63  tff(c_229, plain, (r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_5'), k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3')))) | ~v1_funct_2(k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1(k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_5'))), inference(resolution, [status(thm)], [c_213, c_77])).
% 3.57/1.63  tff(c_250, plain, (r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_5'), k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_219, c_216, c_213, c_229])).
% 3.57/1.63  tff(c_20, plain, (![A_65, F_127, D_121, E_125, B_97, C_113]: (r2_funct_2(u1_struct_0(D_121), u1_struct_0(B_97), k3_tmap_1(A_65, B_97, C_113, D_121, F_127), k2_tmap_1(A_65, B_97, E_125, D_121)) | ~m1_pre_topc(D_121, C_113) | ~r2_funct_2(u1_struct_0(C_113), u1_struct_0(B_97), F_127, k2_tmap_1(A_65, B_97, E_125, C_113)) | ~m1_subset_1(F_127, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_113), u1_struct_0(B_97)))) | ~v1_funct_2(F_127, u1_struct_0(C_113), u1_struct_0(B_97)) | ~v1_funct_1(F_127) | ~m1_subset_1(E_125, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_65), u1_struct_0(B_97)))) | ~v1_funct_2(E_125, u1_struct_0(A_65), u1_struct_0(B_97)) | ~v1_funct_1(E_125) | ~m1_pre_topc(D_121, A_65) | v2_struct_0(D_121) | ~m1_pre_topc(C_113, A_65) | v2_struct_0(C_113) | ~l1_pre_topc(B_97) | ~v2_pre_topc(B_97) | v2_struct_0(B_97) | ~l1_pre_topc(A_65) | ~v2_pre_topc(A_65) | v2_struct_0(A_65))), inference(cnfTransformation, [status(thm)], [f_185])).
% 3.57/1.63  tff(c_384, plain, (![D_121]: (r2_funct_2(u1_struct_0(D_121), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_5', D_121, k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_5')), k2_tmap_1('#skF_2', '#skF_3', '#skF_6', D_121)) | ~m1_pre_topc(D_121, '#skF_5') | ~m1_subset_1(k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3')))) | ~v1_funct_2(k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1(k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_121, '#skF_2') | v2_struct_0(D_121) | ~m1_pre_topc('#skF_5', '#skF_2') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_250, c_20])).
% 3.57/1.63  tff(c_387, plain, (![D_121]: (r2_funct_2(u1_struct_0(D_121), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_5', D_121, k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_5')), k2_tmap_1('#skF_2', '#skF_3', '#skF_6', D_121)) | ~m1_pre_topc(D_121, '#skF_5') | ~m1_pre_topc(D_121, '#skF_2') | v2_struct_0(D_121) | v2_struct_0('#skF_5') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_42, c_40, c_32, c_30, c_28, c_26, c_219, c_216, c_213, c_384])).
% 3.57/1.63  tff(c_769, plain, (![D_265]: (r2_funct_2(u1_struct_0(D_265), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_5', D_265, k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_5')), k2_tmap_1('#skF_2', '#skF_3', '#skF_6', D_265)) | ~m1_pre_topc(D_265, '#skF_5') | ~m1_pre_topc(D_265, '#skF_2') | v2_struct_0(D_265))), inference(negUnitSimplification, [status(thm)], [c_50, c_44, c_34, c_387])).
% 3.57/1.63  tff(c_22, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_5')), k2_tmap_1('#skF_2', '#skF_3', '#skF_6', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_224])).
% 3.57/1.63  tff(c_777, plain, (~m1_pre_topc('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_769, c_22])).
% 3.57/1.63  tff(c_788, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_24, c_777])).
% 3.57/1.63  tff(c_790, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_788])).
% 3.57/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.57/1.63  
% 3.57/1.63  Inference rules
% 3.57/1.63  ----------------------
% 3.57/1.63  #Ref     : 1
% 3.57/1.63  #Sup     : 142
% 3.57/1.63  #Fact    : 0
% 3.57/1.63  #Define  : 0
% 3.57/1.63  #Split   : 3
% 3.57/1.63  #Chain   : 0
% 3.57/1.63  #Close   : 0
% 3.57/1.63  
% 3.57/1.63  Ordering : KBO
% 3.57/1.63  
% 3.57/1.63  Simplification rules
% 3.57/1.63  ----------------------
% 3.57/1.63  #Subsume      : 11
% 3.57/1.63  #Demod        : 443
% 3.57/1.63  #Tautology    : 41
% 3.57/1.63  #SimpNegUnit  : 72
% 3.57/1.63  #BackRed      : 3
% 3.57/1.63  
% 3.57/1.63  #Partial instantiations: 0
% 3.57/1.63  #Strategies tried      : 1
% 3.57/1.63  
% 3.57/1.63  Timing (in seconds)
% 3.57/1.63  ----------------------
% 3.57/1.63  Preprocessing        : 0.37
% 3.57/1.63  Parsing              : 0.20
% 3.57/1.63  CNF conversion       : 0.04
% 3.57/1.63  Main loop            : 0.47
% 3.57/1.63  Inferencing          : 0.16
% 3.57/1.63  Reduction            : 0.16
% 3.57/1.63  Demodulation         : 0.12
% 3.57/1.63  BG Simplification    : 0.03
% 3.57/1.63  Subsumption          : 0.10
% 3.57/1.63  Abstraction          : 0.03
% 3.57/1.63  MUC search           : 0.00
% 3.98/1.63  Cooper               : 0.00
% 3.98/1.63  Total                : 0.87
% 3.98/1.63  Index Insertion      : 0.00
% 3.98/1.63  Index Deletion       : 0.00
% 3.98/1.63  Index Matching       : 0.00
% 3.98/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
