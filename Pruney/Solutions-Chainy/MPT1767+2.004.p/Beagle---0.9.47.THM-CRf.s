%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:16 EST 2020

% Result     : Theorem 4.12s
% Output     : CNFRefutation 4.12s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 767 expanded)
%              Number of leaves         :   29 ( 316 expanded)
%              Depth                    :   28
%              Number of atoms          :  448 (5757 expanded)
%              Number of equality atoms :   22 ( 151 expanded)
%              Maximal formula depth    :   26 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_234,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_tmap_1)).

tff(f_118,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_114,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_tmap_1)).

tff(f_148,axiom,(
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
                  ( ( v1_funct_1(D)
                    & v1_funct_2(D,u1_struct_0(C),u1_struct_0(B))
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                 => r2_funct_2(u1_struct_0(C),u1_struct_0(B),D,k3_tmap_1(A,B,C,C,D)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tmap_1)).

tff(f_195,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tmap_1)).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_32,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_20,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_30,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_44,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_38,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_36,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_28,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_26,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_24,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_22,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_12,plain,(
    ! [A_52] :
      ( m1_pre_topc(A_52,A_52)
      | ~ l1_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_101,plain,(
    ! [E_188,A_191,C_190,D_189,B_187] :
      ( k3_tmap_1(A_191,B_187,C_190,D_189,E_188) = k2_partfun1(u1_struct_0(C_190),u1_struct_0(B_187),E_188,u1_struct_0(D_189))
      | ~ m1_pre_topc(D_189,C_190)
      | ~ m1_subset_1(E_188,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_190),u1_struct_0(B_187))))
      | ~ v1_funct_2(E_188,u1_struct_0(C_190),u1_struct_0(B_187))
      | ~ v1_funct_1(E_188)
      | ~ m1_pre_topc(D_189,A_191)
      | ~ m1_pre_topc(C_190,A_191)
      | ~ l1_pre_topc(B_187)
      | ~ v2_pre_topc(B_187)
      | v2_struct_0(B_187)
      | ~ l1_pre_topc(A_191)
      | ~ v2_pre_topc(A_191)
      | v2_struct_0(A_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_105,plain,(
    ! [A_191,D_189] :
      ( k3_tmap_1(A_191,'#skF_2','#skF_1',D_189,'#skF_5') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_189))
      | ~ m1_pre_topc(D_189,'#skF_1')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_189,A_191)
      | ~ m1_pre_topc('#skF_1',A_191)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_191)
      | ~ v2_pre_topc(A_191)
      | v2_struct_0(A_191) ) ),
    inference(resolution,[status(thm)],[c_22,c_101])).

tff(c_109,plain,(
    ! [A_191,D_189] :
      ( k3_tmap_1(A_191,'#skF_2','#skF_1',D_189,'#skF_5') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_189))
      | ~ m1_pre_topc(D_189,'#skF_1')
      | ~ m1_pre_topc(D_189,A_191)
      | ~ m1_pre_topc('#skF_1',A_191)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_191)
      | ~ v2_pre_topc(A_191)
      | v2_struct_0(A_191) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_26,c_24,c_105])).

tff(c_111,plain,(
    ! [A_192,D_193] :
      ( k3_tmap_1(A_192,'#skF_2','#skF_1',D_193,'#skF_5') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_193))
      | ~ m1_pre_topc(D_193,'#skF_1')
      | ~ m1_pre_topc(D_193,A_192)
      | ~ m1_pre_topc('#skF_1',A_192)
      | ~ l1_pre_topc(A_192)
      | ~ v2_pre_topc(A_192)
      | v2_struct_0(A_192) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_109])).

tff(c_117,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_111])).

tff(c_127,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_28,c_117])).

tff(c_128,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_127])).

tff(c_133,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_136,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_133])).

tff(c_140,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_136])).

tff(c_142,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_141,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_56,plain,(
    ! [A_165,B_166,C_167,D_168] :
      ( k2_partfun1(u1_struct_0(A_165),u1_struct_0(B_166),C_167,u1_struct_0(D_168)) = k2_tmap_1(A_165,B_166,C_167,D_168)
      | ~ m1_pre_topc(D_168,A_165)
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_165),u1_struct_0(B_166))))
      | ~ v1_funct_2(C_167,u1_struct_0(A_165),u1_struct_0(B_166))
      | ~ v1_funct_1(C_167)
      | ~ l1_pre_topc(B_166)
      | ~ v2_pre_topc(B_166)
      | v2_struct_0(B_166)
      | ~ l1_pre_topc(A_165)
      | ~ v2_pre_topc(A_165)
      | v2_struct_0(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_58,plain,(
    ! [D_168] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_168)) = k2_tmap_1('#skF_1','#skF_2','#skF_5',D_168)
      | ~ m1_pre_topc(D_168,'#skF_1')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_22,c_56])).

tff(c_61,plain,(
    ! [D_168] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_168)) = k2_tmap_1('#skF_1','#skF_2','#skF_5',D_168)
      | ~ m1_pre_topc(D_168,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_38,c_36,c_26,c_24,c_58])).

tff(c_62,plain,(
    ! [D_168] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_168)) = k2_tmap_1('#skF_1','#skF_2','#skF_5',D_168)
      | ~ m1_pre_topc(D_168,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_40,c_61])).

tff(c_164,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_62])).

tff(c_171,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_164])).

tff(c_48,plain,(
    ! [B_161,C_162,D_160,E_159,A_158] :
      ( v1_funct_1(k3_tmap_1(A_158,B_161,C_162,D_160,E_159))
      | ~ m1_subset_1(E_159,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_162),u1_struct_0(B_161))))
      | ~ v1_funct_2(E_159,u1_struct_0(C_162),u1_struct_0(B_161))
      | ~ v1_funct_1(E_159)
      | ~ m1_pre_topc(D_160,A_158)
      | ~ m1_pre_topc(C_162,A_158)
      | ~ l1_pre_topc(B_161)
      | ~ v2_pre_topc(B_161)
      | v2_struct_0(B_161)
      | ~ l1_pre_topc(A_158)
      | ~ v2_pre_topc(A_158)
      | v2_struct_0(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_50,plain,(
    ! [A_158,D_160] :
      ( v1_funct_1(k3_tmap_1(A_158,'#skF_2','#skF_1',D_160,'#skF_5'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_160,A_158)
      | ~ m1_pre_topc('#skF_1',A_158)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_158)
      | ~ v2_pre_topc(A_158)
      | v2_struct_0(A_158) ) ),
    inference(resolution,[status(thm)],[c_22,c_48])).

tff(c_53,plain,(
    ! [A_158,D_160] :
      ( v1_funct_1(k3_tmap_1(A_158,'#skF_2','#skF_1',D_160,'#skF_5'))
      | ~ m1_pre_topc(D_160,A_158)
      | ~ m1_pre_topc('#skF_1',A_158)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_158)
      | ~ v2_pre_topc(A_158)
      | v2_struct_0(A_158) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_26,c_24,c_50])).

tff(c_54,plain,(
    ! [A_158,D_160] :
      ( v1_funct_1(k3_tmap_1(A_158,'#skF_2','#skF_1',D_160,'#skF_5'))
      | ~ m1_pre_topc(D_160,A_158)
      | ~ m1_pre_topc('#skF_1',A_158)
      | ~ l1_pre_topc(A_158)
      | ~ v2_pre_topc(A_158)
      | v2_struct_0(A_158) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_53])).

tff(c_186,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_54])).

tff(c_196,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_142,c_28,c_186])).

tff(c_197,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_196])).

tff(c_80,plain,(
    ! [D_177,B_178,A_175,E_176,C_179] :
      ( v1_funct_2(k3_tmap_1(A_175,B_178,C_179,D_177,E_176),u1_struct_0(D_177),u1_struct_0(B_178))
      | ~ m1_subset_1(E_176,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_179),u1_struct_0(B_178))))
      | ~ v1_funct_2(E_176,u1_struct_0(C_179),u1_struct_0(B_178))
      | ~ v1_funct_1(E_176)
      | ~ m1_pre_topc(D_177,A_175)
      | ~ m1_pre_topc(C_179,A_175)
      | ~ l1_pre_topc(B_178)
      | ~ v2_pre_topc(B_178)
      | v2_struct_0(B_178)
      | ~ l1_pre_topc(A_175)
      | ~ v2_pre_topc(A_175)
      | v2_struct_0(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_82,plain,(
    ! [A_175,D_177] :
      ( v1_funct_2(k3_tmap_1(A_175,'#skF_2','#skF_1',D_177,'#skF_5'),u1_struct_0(D_177),u1_struct_0('#skF_2'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_177,A_175)
      | ~ m1_pre_topc('#skF_1',A_175)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_175)
      | ~ v2_pre_topc(A_175)
      | v2_struct_0(A_175) ) ),
    inference(resolution,[status(thm)],[c_22,c_80])).

tff(c_85,plain,(
    ! [A_175,D_177] :
      ( v1_funct_2(k3_tmap_1(A_175,'#skF_2','#skF_1',D_177,'#skF_5'),u1_struct_0(D_177),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_177,A_175)
      | ~ m1_pre_topc('#skF_1',A_175)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_175)
      | ~ v2_pre_topc(A_175)
      | v2_struct_0(A_175) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_26,c_24,c_82])).

tff(c_86,plain,(
    ! [A_175,D_177] :
      ( v1_funct_2(k3_tmap_1(A_175,'#skF_2','#skF_1',D_177,'#skF_5'),u1_struct_0(D_177),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_177,A_175)
      | ~ m1_pre_topc('#skF_1',A_175)
      | ~ l1_pre_topc(A_175)
      | ~ v2_pre_topc(A_175)
      | v2_struct_0(A_175) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_85])).

tff(c_183,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_86])).

tff(c_193,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_142,c_28,c_183])).

tff(c_194,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_193])).

tff(c_6,plain,(
    ! [A_47,E_51,D_50,C_49,B_48] :
      ( m1_subset_1(k3_tmap_1(A_47,B_48,C_49,D_50,E_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_50),u1_struct_0(B_48))))
      | ~ m1_subset_1(E_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_49),u1_struct_0(B_48))))
      | ~ v1_funct_2(E_51,u1_struct_0(C_49),u1_struct_0(B_48))
      | ~ v1_funct_1(E_51)
      | ~ m1_pre_topc(D_50,A_47)
      | ~ m1_pre_topc(C_49,A_47)
      | ~ l1_pre_topc(B_48)
      | ~ v2_pre_topc(B_48)
      | v2_struct_0(B_48)
      | ~ l1_pre_topc(A_47)
      | ~ v2_pre_topc(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_180,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_6])).

tff(c_190,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_38,c_36,c_142,c_28,c_26,c_24,c_22,c_180])).

tff(c_191,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_40,c_190])).

tff(c_110,plain,(
    ! [A_191,D_189] :
      ( k3_tmap_1(A_191,'#skF_2','#skF_1',D_189,'#skF_5') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_189))
      | ~ m1_pre_topc(D_189,'#skF_1')
      | ~ m1_pre_topc(D_189,A_191)
      | ~ m1_pre_topc('#skF_1',A_191)
      | ~ l1_pre_topc(A_191)
      | ~ v2_pre_topc(A_191)
      | v2_struct_0(A_191) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_109])).

tff(c_155,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_1')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_5')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_142,c_110])).

tff(c_158,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_1')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_142,c_155])).

tff(c_159,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_1')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_158])).

tff(c_334,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_62])).

tff(c_341,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_334])).

tff(c_72,plain,(
    ! [C_170,B_171,D_172,A_173] :
      ( r2_funct_2(u1_struct_0(C_170),u1_struct_0(B_171),D_172,k3_tmap_1(A_173,B_171,C_170,C_170,D_172))
      | ~ m1_subset_1(D_172,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_170),u1_struct_0(B_171))))
      | ~ v1_funct_2(D_172,u1_struct_0(C_170),u1_struct_0(B_171))
      | ~ v1_funct_1(D_172)
      | ~ m1_pre_topc(C_170,A_173)
      | v2_struct_0(C_170)
      | ~ l1_pre_topc(B_171)
      | ~ v2_pre_topc(B_171)
      | v2_struct_0(B_171)
      | ~ l1_pre_topc(A_173)
      | ~ v2_pre_topc(A_173)
      | v2_struct_0(A_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_74,plain,(
    ! [A_173] :
      ( r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',k3_tmap_1(A_173,'#skF_2','#skF_1','#skF_1','#skF_5'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_1',A_173)
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_173)
      | ~ v2_pre_topc(A_173)
      | v2_struct_0(A_173) ) ),
    inference(resolution,[status(thm)],[c_22,c_72])).

tff(c_77,plain,(
    ! [A_173] :
      ( r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',k3_tmap_1(A_173,'#skF_2','#skF_1','#skF_1','#skF_5'))
      | ~ m1_pre_topc('#skF_1',A_173)
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_173)
      | ~ v2_pre_topc(A_173)
      | v2_struct_0(A_173) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_26,c_24,c_74])).

tff(c_78,plain,(
    ! [A_173] :
      ( r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',k3_tmap_1(A_173,'#skF_2','#skF_1','#skF_1','#skF_5'))
      | ~ m1_pre_topc('#skF_1',A_173)
      | ~ l1_pre_topc(A_173)
      | ~ v2_pre_topc(A_173)
      | v2_struct_0(A_173) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_46,c_77])).

tff(c_357,plain,
    ( r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'))
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_341,c_78])).

tff(c_373,plain,
    ( r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_142,c_357])).

tff(c_374,plain,(
    r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_373])).

tff(c_16,plain,(
    ! [F_130,D_124,B_100,C_116,A_68,E_128] :
      ( r2_funct_2(u1_struct_0(D_124),u1_struct_0(B_100),k3_tmap_1(A_68,B_100,C_116,D_124,F_130),k2_tmap_1(A_68,B_100,E_128,D_124))
      | ~ m1_pre_topc(D_124,C_116)
      | ~ r2_funct_2(u1_struct_0(C_116),u1_struct_0(B_100),F_130,k2_tmap_1(A_68,B_100,E_128,C_116))
      | ~ m1_subset_1(F_130,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_116),u1_struct_0(B_100))))
      | ~ v1_funct_2(F_130,u1_struct_0(C_116),u1_struct_0(B_100))
      | ~ v1_funct_1(F_130)
      | ~ m1_subset_1(E_128,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_68),u1_struct_0(B_100))))
      | ~ v1_funct_2(E_128,u1_struct_0(A_68),u1_struct_0(B_100))
      | ~ v1_funct_1(E_128)
      | ~ m1_pre_topc(D_124,A_68)
      | v2_struct_0(D_124)
      | ~ m1_pre_topc(C_116,A_68)
      | v2_struct_0(C_116)
      | ~ l1_pre_topc(B_100)
      | ~ v2_pre_topc(B_100)
      | v2_struct_0(B_100)
      | ~ l1_pre_topc(A_68)
      | ~ v2_pre_topc(A_68)
      | v2_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_381,plain,(
    ! [D_124] :
      ( r2_funct_2(u1_struct_0(D_124),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_1',D_124,'#skF_5'),k2_tmap_1('#skF_1','#skF_2','#skF_5',D_124))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_124,'#skF_1')
      | v2_struct_0(D_124)
      | ~ m1_pre_topc('#skF_1','#skF_1')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_374,c_16])).

tff(c_384,plain,(
    ! [D_124] :
      ( r2_funct_2(u1_struct_0(D_124),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_1',D_124,'#skF_5'),k2_tmap_1('#skF_1','#skF_2','#skF_5',D_124))
      | ~ m1_pre_topc(D_124,'#skF_1')
      | v2_struct_0(D_124)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_38,c_36,c_142,c_26,c_24,c_22,c_381])).

tff(c_472,plain,(
    ! [D_214] :
      ( r2_funct_2(u1_struct_0(D_214),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_1',D_214,'#skF_5'),k2_tmap_1('#skF_1','#skF_2','#skF_5',D_214))
      | ~ m1_pre_topc(D_214,'#skF_1')
      | v2_struct_0(D_214) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_40,c_384])).

tff(c_483,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_472])).

tff(c_495,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_483])).

tff(c_496,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_495])).

tff(c_510,plain,(
    ! [D_124] :
      ( r2_funct_2(u1_struct_0(D_124),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4',D_124,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k2_tmap_1('#skF_1','#skF_2','#skF_5',D_124))
      | ~ m1_pre_topc(D_124,'#skF_4')
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_124,'#skF_1')
      | v2_struct_0(D_124)
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_496,c_16])).

tff(c_513,plain,(
    ! [D_124] :
      ( r2_funct_2(u1_struct_0(D_124),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4',D_124,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k2_tmap_1('#skF_1','#skF_2','#skF_5',D_124))
      | ~ m1_pre_topc(D_124,'#skF_4')
      | ~ m1_pre_topc(D_124,'#skF_1')
      | v2_struct_0(D_124)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_38,c_36,c_28,c_26,c_24,c_22,c_197,c_194,c_191,c_510])).

tff(c_776,plain,(
    ! [D_251] :
      ( r2_funct_2(u1_struct_0(D_251),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4',D_251,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k2_tmap_1('#skF_1','#skF_2','#skF_5',D_251))
      | ~ m1_pre_topc(D_251,'#skF_4')
      | ~ m1_pre_topc(D_251,'#skF_1')
      | v2_struct_0(D_251) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_40,c_30,c_513])).

tff(c_18,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_781,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_776,c_18])).

tff(c_788,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_20,c_781])).

tff(c_790,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_788])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:03:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.12/1.70  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.12/1.71  
% 4.12/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.12/1.71  %$ r2_funct_2 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.12/1.71  
% 4.12/1.71  %Foreground sorts:
% 4.12/1.71  
% 4.12/1.71  
% 4.12/1.71  %Background operators:
% 4.12/1.71  
% 4.12/1.71  
% 4.12/1.71  %Foreground operators:
% 4.12/1.71  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.12/1.71  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.12/1.71  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.12/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.12/1.71  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.12/1.71  tff('#skF_5', type, '#skF_5': $i).
% 4.12/1.71  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.12/1.71  tff('#skF_2', type, '#skF_2': $i).
% 4.12/1.71  tff('#skF_3', type, '#skF_3': $i).
% 4.12/1.71  tff('#skF_1', type, '#skF_1': $i).
% 4.12/1.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.12/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.12/1.71  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.12/1.71  tff('#skF_4', type, '#skF_4': $i).
% 4.12/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.12/1.71  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.12/1.71  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 4.12/1.71  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.12/1.71  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 4.12/1.71  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.12/1.71  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 4.12/1.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.12/1.71  
% 4.12/1.73  tff(f_234, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (m1_pre_topc(C, D) => r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, D, C, k2_tmap_1(A, B, E, D)), k2_tmap_1(A, B, E, C))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_tmap_1)).
% 4.12/1.73  tff(f_118, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 4.12/1.73  tff(f_84, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 4.12/1.73  tff(f_52, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 4.12/1.73  tff(f_114, axiom, (![A, B, C, D, E]: (((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & m1_pre_topc(C, A)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((v1_funct_1(k3_tmap_1(A, B, C, D, E)) & v1_funct_2(k3_tmap_1(A, B, C, D, E), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k3_tmap_1(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 4.12/1.73  tff(f_148, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => r2_funct_2(u1_struct_0(C), u1_struct_0(B), D, k3_tmap_1(A, B, C, C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tmap_1)).
% 4.12/1.73  tff(f_195, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((r2_funct_2(u1_struct_0(C), u1_struct_0(B), F, k2_tmap_1(A, B, E, C)) & m1_pre_topc(D, C)) => r2_funct_2(u1_struct_0(D), u1_struct_0(B), k3_tmap_1(A, B, C, D, F), k2_tmap_1(A, B, E, D))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tmap_1)).
% 4.12/1.73  tff(c_34, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_234])).
% 4.12/1.73  tff(c_32, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_234])).
% 4.12/1.73  tff(c_20, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_234])).
% 4.12/1.73  tff(c_46, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_234])).
% 4.12/1.73  tff(c_40, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_234])).
% 4.12/1.73  tff(c_30, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_234])).
% 4.12/1.73  tff(c_44, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_234])).
% 4.12/1.73  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_234])).
% 4.12/1.73  tff(c_38, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_234])).
% 4.12/1.73  tff(c_36, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_234])).
% 4.12/1.73  tff(c_28, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_234])).
% 4.12/1.73  tff(c_26, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_234])).
% 4.12/1.73  tff(c_24, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_234])).
% 4.12/1.73  tff(c_22, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_234])).
% 4.12/1.73  tff(c_12, plain, (![A_52]: (m1_pre_topc(A_52, A_52) | ~l1_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.12/1.73  tff(c_101, plain, (![E_188, A_191, C_190, D_189, B_187]: (k3_tmap_1(A_191, B_187, C_190, D_189, E_188)=k2_partfun1(u1_struct_0(C_190), u1_struct_0(B_187), E_188, u1_struct_0(D_189)) | ~m1_pre_topc(D_189, C_190) | ~m1_subset_1(E_188, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_190), u1_struct_0(B_187)))) | ~v1_funct_2(E_188, u1_struct_0(C_190), u1_struct_0(B_187)) | ~v1_funct_1(E_188) | ~m1_pre_topc(D_189, A_191) | ~m1_pre_topc(C_190, A_191) | ~l1_pre_topc(B_187) | ~v2_pre_topc(B_187) | v2_struct_0(B_187) | ~l1_pre_topc(A_191) | ~v2_pre_topc(A_191) | v2_struct_0(A_191))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.12/1.73  tff(c_105, plain, (![A_191, D_189]: (k3_tmap_1(A_191, '#skF_2', '#skF_1', D_189, '#skF_5')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_189)) | ~m1_pre_topc(D_189, '#skF_1') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_189, A_191) | ~m1_pre_topc('#skF_1', A_191) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_191) | ~v2_pre_topc(A_191) | v2_struct_0(A_191))), inference(resolution, [status(thm)], [c_22, c_101])).
% 4.12/1.73  tff(c_109, plain, (![A_191, D_189]: (k3_tmap_1(A_191, '#skF_2', '#skF_1', D_189, '#skF_5')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_189)) | ~m1_pre_topc(D_189, '#skF_1') | ~m1_pre_topc(D_189, A_191) | ~m1_pre_topc('#skF_1', A_191) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_191) | ~v2_pre_topc(A_191) | v2_struct_0(A_191))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_26, c_24, c_105])).
% 4.12/1.73  tff(c_111, plain, (![A_192, D_193]: (k3_tmap_1(A_192, '#skF_2', '#skF_1', D_193, '#skF_5')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_193)) | ~m1_pre_topc(D_193, '#skF_1') | ~m1_pre_topc(D_193, A_192) | ~m1_pre_topc('#skF_1', A_192) | ~l1_pre_topc(A_192) | ~v2_pre_topc(A_192) | v2_struct_0(A_192))), inference(negUnitSimplification, [status(thm)], [c_40, c_109])).
% 4.12/1.73  tff(c_117, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_28, c_111])).
% 4.12/1.73  tff(c_127, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_28, c_117])).
% 4.12/1.73  tff(c_128, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_46, c_127])).
% 4.12/1.73  tff(c_133, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_128])).
% 4.12/1.73  tff(c_136, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12, c_133])).
% 4.12/1.73  tff(c_140, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_136])).
% 4.12/1.73  tff(c_142, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_128])).
% 4.12/1.73  tff(c_141, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_128])).
% 4.12/1.73  tff(c_56, plain, (![A_165, B_166, C_167, D_168]: (k2_partfun1(u1_struct_0(A_165), u1_struct_0(B_166), C_167, u1_struct_0(D_168))=k2_tmap_1(A_165, B_166, C_167, D_168) | ~m1_pre_topc(D_168, A_165) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_165), u1_struct_0(B_166)))) | ~v1_funct_2(C_167, u1_struct_0(A_165), u1_struct_0(B_166)) | ~v1_funct_1(C_167) | ~l1_pre_topc(B_166) | ~v2_pre_topc(B_166) | v2_struct_0(B_166) | ~l1_pre_topc(A_165) | ~v2_pre_topc(A_165) | v2_struct_0(A_165))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.12/1.73  tff(c_58, plain, (![D_168]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_168))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_168) | ~m1_pre_topc(D_168, '#skF_1') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_56])).
% 4.12/1.73  tff(c_61, plain, (![D_168]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_168))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_168) | ~m1_pre_topc(D_168, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_38, c_36, c_26, c_24, c_58])).
% 4.12/1.73  tff(c_62, plain, (![D_168]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_168))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_168) | ~m1_pre_topc(D_168, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_46, c_40, c_61])).
% 4.12/1.73  tff(c_164, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_141, c_62])).
% 4.12/1.73  tff(c_171, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_164])).
% 4.12/1.73  tff(c_48, plain, (![B_161, C_162, D_160, E_159, A_158]: (v1_funct_1(k3_tmap_1(A_158, B_161, C_162, D_160, E_159)) | ~m1_subset_1(E_159, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_162), u1_struct_0(B_161)))) | ~v1_funct_2(E_159, u1_struct_0(C_162), u1_struct_0(B_161)) | ~v1_funct_1(E_159) | ~m1_pre_topc(D_160, A_158) | ~m1_pre_topc(C_162, A_158) | ~l1_pre_topc(B_161) | ~v2_pre_topc(B_161) | v2_struct_0(B_161) | ~l1_pre_topc(A_158) | ~v2_pre_topc(A_158) | v2_struct_0(A_158))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.12/1.73  tff(c_50, plain, (![A_158, D_160]: (v1_funct_1(k3_tmap_1(A_158, '#skF_2', '#skF_1', D_160, '#skF_5')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_160, A_158) | ~m1_pre_topc('#skF_1', A_158) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_158) | ~v2_pre_topc(A_158) | v2_struct_0(A_158))), inference(resolution, [status(thm)], [c_22, c_48])).
% 4.12/1.73  tff(c_53, plain, (![A_158, D_160]: (v1_funct_1(k3_tmap_1(A_158, '#skF_2', '#skF_1', D_160, '#skF_5')) | ~m1_pre_topc(D_160, A_158) | ~m1_pre_topc('#skF_1', A_158) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_158) | ~v2_pre_topc(A_158) | v2_struct_0(A_158))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_26, c_24, c_50])).
% 4.12/1.73  tff(c_54, plain, (![A_158, D_160]: (v1_funct_1(k3_tmap_1(A_158, '#skF_2', '#skF_1', D_160, '#skF_5')) | ~m1_pre_topc(D_160, A_158) | ~m1_pre_topc('#skF_1', A_158) | ~l1_pre_topc(A_158) | ~v2_pre_topc(A_158) | v2_struct_0(A_158))), inference(negUnitSimplification, [status(thm)], [c_40, c_53])).
% 4.12/1.73  tff(c_186, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_171, c_54])).
% 4.12/1.73  tff(c_196, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_142, c_28, c_186])).
% 4.12/1.73  tff(c_197, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_46, c_196])).
% 4.12/1.73  tff(c_80, plain, (![D_177, B_178, A_175, E_176, C_179]: (v1_funct_2(k3_tmap_1(A_175, B_178, C_179, D_177, E_176), u1_struct_0(D_177), u1_struct_0(B_178)) | ~m1_subset_1(E_176, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_179), u1_struct_0(B_178)))) | ~v1_funct_2(E_176, u1_struct_0(C_179), u1_struct_0(B_178)) | ~v1_funct_1(E_176) | ~m1_pre_topc(D_177, A_175) | ~m1_pre_topc(C_179, A_175) | ~l1_pre_topc(B_178) | ~v2_pre_topc(B_178) | v2_struct_0(B_178) | ~l1_pre_topc(A_175) | ~v2_pre_topc(A_175) | v2_struct_0(A_175))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.12/1.73  tff(c_82, plain, (![A_175, D_177]: (v1_funct_2(k3_tmap_1(A_175, '#skF_2', '#skF_1', D_177, '#skF_5'), u1_struct_0(D_177), u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_177, A_175) | ~m1_pre_topc('#skF_1', A_175) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_175) | ~v2_pre_topc(A_175) | v2_struct_0(A_175))), inference(resolution, [status(thm)], [c_22, c_80])).
% 4.12/1.73  tff(c_85, plain, (![A_175, D_177]: (v1_funct_2(k3_tmap_1(A_175, '#skF_2', '#skF_1', D_177, '#skF_5'), u1_struct_0(D_177), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_177, A_175) | ~m1_pre_topc('#skF_1', A_175) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_175) | ~v2_pre_topc(A_175) | v2_struct_0(A_175))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_26, c_24, c_82])).
% 4.12/1.73  tff(c_86, plain, (![A_175, D_177]: (v1_funct_2(k3_tmap_1(A_175, '#skF_2', '#skF_1', D_177, '#skF_5'), u1_struct_0(D_177), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_177, A_175) | ~m1_pre_topc('#skF_1', A_175) | ~l1_pre_topc(A_175) | ~v2_pre_topc(A_175) | v2_struct_0(A_175))), inference(negUnitSimplification, [status(thm)], [c_40, c_85])).
% 4.12/1.73  tff(c_183, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_171, c_86])).
% 4.12/1.73  tff(c_193, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_142, c_28, c_183])).
% 4.12/1.73  tff(c_194, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_46, c_193])).
% 4.12/1.73  tff(c_6, plain, (![A_47, E_51, D_50, C_49, B_48]: (m1_subset_1(k3_tmap_1(A_47, B_48, C_49, D_50, E_51), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_50), u1_struct_0(B_48)))) | ~m1_subset_1(E_51, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_49), u1_struct_0(B_48)))) | ~v1_funct_2(E_51, u1_struct_0(C_49), u1_struct_0(B_48)) | ~v1_funct_1(E_51) | ~m1_pre_topc(D_50, A_47) | ~m1_pre_topc(C_49, A_47) | ~l1_pre_topc(B_48) | ~v2_pre_topc(B_48) | v2_struct_0(B_48) | ~l1_pre_topc(A_47) | ~v2_pre_topc(A_47) | v2_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.12/1.73  tff(c_180, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_171, c_6])).
% 4.12/1.73  tff(c_190, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_38, c_36, c_142, c_28, c_26, c_24, c_22, c_180])).
% 4.12/1.73  tff(c_191, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_46, c_40, c_190])).
% 4.12/1.73  tff(c_110, plain, (![A_191, D_189]: (k3_tmap_1(A_191, '#skF_2', '#skF_1', D_189, '#skF_5')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_189)) | ~m1_pre_topc(D_189, '#skF_1') | ~m1_pre_topc(D_189, A_191) | ~m1_pre_topc('#skF_1', A_191) | ~l1_pre_topc(A_191) | ~v2_pre_topc(A_191) | v2_struct_0(A_191))), inference(negUnitSimplification, [status(thm)], [c_40, c_109])).
% 4.12/1.73  tff(c_155, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_1'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_5') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_142, c_110])).
% 4.12/1.73  tff(c_158, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_1'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_142, c_155])).
% 4.12/1.73  tff(c_159, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_1'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_46, c_158])).
% 4.12/1.73  tff(c_334, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_159, c_62])).
% 4.12/1.73  tff(c_341, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_334])).
% 4.12/1.73  tff(c_72, plain, (![C_170, B_171, D_172, A_173]: (r2_funct_2(u1_struct_0(C_170), u1_struct_0(B_171), D_172, k3_tmap_1(A_173, B_171, C_170, C_170, D_172)) | ~m1_subset_1(D_172, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_170), u1_struct_0(B_171)))) | ~v1_funct_2(D_172, u1_struct_0(C_170), u1_struct_0(B_171)) | ~v1_funct_1(D_172) | ~m1_pre_topc(C_170, A_173) | v2_struct_0(C_170) | ~l1_pre_topc(B_171) | ~v2_pre_topc(B_171) | v2_struct_0(B_171) | ~l1_pre_topc(A_173) | ~v2_pre_topc(A_173) | v2_struct_0(A_173))), inference(cnfTransformation, [status(thm)], [f_148])).
% 4.12/1.73  tff(c_74, plain, (![A_173]: (r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', k3_tmap_1(A_173, '#skF_2', '#skF_1', '#skF_1', '#skF_5')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_1', A_173) | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_173) | ~v2_pre_topc(A_173) | v2_struct_0(A_173))), inference(resolution, [status(thm)], [c_22, c_72])).
% 4.12/1.73  tff(c_77, plain, (![A_173]: (r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', k3_tmap_1(A_173, '#skF_2', '#skF_1', '#skF_1', '#skF_5')) | ~m1_pre_topc('#skF_1', A_173) | v2_struct_0('#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_173) | ~v2_pre_topc(A_173) | v2_struct_0(A_173))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_26, c_24, c_74])).
% 4.12/1.73  tff(c_78, plain, (![A_173]: (r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', k3_tmap_1(A_173, '#skF_2', '#skF_1', '#skF_1', '#skF_5')) | ~m1_pre_topc('#skF_1', A_173) | ~l1_pre_topc(A_173) | ~v2_pre_topc(A_173) | v2_struct_0(A_173))), inference(negUnitSimplification, [status(thm)], [c_40, c_46, c_77])).
% 4.12/1.73  tff(c_357, plain, (r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1')) | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_341, c_78])).
% 4.12/1.73  tff(c_373, plain, (r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_142, c_357])).
% 4.12/1.73  tff(c_374, plain, (r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_46, c_373])).
% 4.12/1.73  tff(c_16, plain, (![F_130, D_124, B_100, C_116, A_68, E_128]: (r2_funct_2(u1_struct_0(D_124), u1_struct_0(B_100), k3_tmap_1(A_68, B_100, C_116, D_124, F_130), k2_tmap_1(A_68, B_100, E_128, D_124)) | ~m1_pre_topc(D_124, C_116) | ~r2_funct_2(u1_struct_0(C_116), u1_struct_0(B_100), F_130, k2_tmap_1(A_68, B_100, E_128, C_116)) | ~m1_subset_1(F_130, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_116), u1_struct_0(B_100)))) | ~v1_funct_2(F_130, u1_struct_0(C_116), u1_struct_0(B_100)) | ~v1_funct_1(F_130) | ~m1_subset_1(E_128, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_68), u1_struct_0(B_100)))) | ~v1_funct_2(E_128, u1_struct_0(A_68), u1_struct_0(B_100)) | ~v1_funct_1(E_128) | ~m1_pre_topc(D_124, A_68) | v2_struct_0(D_124) | ~m1_pre_topc(C_116, A_68) | v2_struct_0(C_116) | ~l1_pre_topc(B_100) | ~v2_pre_topc(B_100) | v2_struct_0(B_100) | ~l1_pre_topc(A_68) | ~v2_pre_topc(A_68) | v2_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.12/1.73  tff(c_381, plain, (![D_124]: (r2_funct_2(u1_struct_0(D_124), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_1', D_124, '#skF_5'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_124)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_124, '#skF_1') | v2_struct_0(D_124) | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_374, c_16])).
% 4.12/1.73  tff(c_384, plain, (![D_124]: (r2_funct_2(u1_struct_0(D_124), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_1', D_124, '#skF_5'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_124)) | ~m1_pre_topc(D_124, '#skF_1') | v2_struct_0(D_124) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_38, c_36, c_142, c_26, c_24, c_22, c_381])).
% 4.12/1.73  tff(c_472, plain, (![D_214]: (r2_funct_2(u1_struct_0(D_214), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_1', D_214, '#skF_5'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_214)) | ~m1_pre_topc(D_214, '#skF_1') | v2_struct_0(D_214))), inference(negUnitSimplification, [status(thm)], [c_46, c_40, c_384])).
% 4.12/1.73  tff(c_483, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_171, c_472])).
% 4.12/1.73  tff(c_495, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_483])).
% 4.12/1.73  tff(c_496, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_30, c_495])).
% 4.12/1.73  tff(c_510, plain, (![D_124]: (r2_funct_2(u1_struct_0(D_124), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', D_124, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_124)) | ~m1_pre_topc(D_124, '#skF_4') | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_124, '#skF_1') | v2_struct_0(D_124) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_496, c_16])).
% 4.12/1.73  tff(c_513, plain, (![D_124]: (r2_funct_2(u1_struct_0(D_124), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', D_124, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_124)) | ~m1_pre_topc(D_124, '#skF_4') | ~m1_pre_topc(D_124, '#skF_1') | v2_struct_0(D_124) | v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_38, c_36, c_28, c_26, c_24, c_22, c_197, c_194, c_191, c_510])).
% 4.12/1.73  tff(c_776, plain, (![D_251]: (r2_funct_2(u1_struct_0(D_251), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', D_251, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_251)) | ~m1_pre_topc(D_251, '#skF_4') | ~m1_pre_topc(D_251, '#skF_1') | v2_struct_0(D_251))), inference(negUnitSimplification, [status(thm)], [c_46, c_40, c_30, c_513])).
% 4.12/1.73  tff(c_18, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_234])).
% 4.12/1.73  tff(c_781, plain, (~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_776, c_18])).
% 4.12/1.73  tff(c_788, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_20, c_781])).
% 4.12/1.73  tff(c_790, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_788])).
% 4.12/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.12/1.73  
% 4.12/1.73  Inference rules
% 4.12/1.73  ----------------------
% 4.12/1.73  #Ref     : 0
% 4.12/1.73  #Sup     : 138
% 4.12/1.73  #Fact    : 0
% 4.12/1.73  #Define  : 0
% 4.12/1.73  #Split   : 4
% 4.12/1.73  #Chain   : 0
% 4.12/1.73  #Close   : 0
% 4.12/1.73  
% 4.12/1.73  Ordering : KBO
% 4.12/1.73  
% 4.12/1.73  Simplification rules
% 4.12/1.73  ----------------------
% 4.12/1.73  #Subsume      : 12
% 4.12/1.73  #Demod        : 507
% 4.12/1.73  #Tautology    : 40
% 4.12/1.73  #SimpNegUnit  : 86
% 4.12/1.73  #BackRed      : 3
% 4.12/1.73  
% 4.12/1.73  #Partial instantiations: 0
% 4.12/1.73  #Strategies tried      : 1
% 4.12/1.73  
% 4.12/1.73  Timing (in seconds)
% 4.12/1.73  ----------------------
% 4.12/1.73  Preprocessing        : 0.40
% 4.12/1.73  Parsing              : 0.22
% 4.12/1.73  CNF conversion       : 0.05
% 4.12/1.73  Main loop            : 0.52
% 4.12/1.73  Inferencing          : 0.18
% 4.12/1.73  Reduction            : 0.18
% 4.12/1.73  Demodulation         : 0.14
% 4.12/1.73  BG Simplification    : 0.03
% 4.12/1.74  Subsumption          : 0.11
% 4.12/1.74  Abstraction          : 0.03
% 4.12/1.74  MUC search           : 0.00
% 4.12/1.74  Cooper               : 0.00
% 4.12/1.74  Total                : 0.96
% 4.12/1.74  Index Insertion      : 0.00
% 4.12/1.74  Index Deletion       : 0.00
% 4.12/1.74  Index Matching       : 0.00
% 4.12/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
