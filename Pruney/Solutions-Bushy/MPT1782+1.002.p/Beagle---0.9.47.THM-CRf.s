%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1782+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:22 EST 2020

% Result     : Theorem 6.85s
% Output     : CNFRefutation 7.23s
% Verified   : 
% Statistics : Number of formulae       :  134 (3842 expanded)
%              Number of leaves         :   40 (1388 expanded)
%              Depth                    :   32
%              Number of atoms          :  381 (15743 expanded)
%              Number of equality atoms :   25 (1106 expanded)
%              Maximal formula depth    :   27 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > r2_funct_2 > v1_funct_2 > v1_partfun1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k4_relset_1 > k1_partfun1 > k2_tmap_1 > k5_relat_1 > k4_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_partfun1 > k3_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k4_tmap_1,type,(
    k4_tmap_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k4_relset_1,type,(
    k4_relset_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(k3_struct_0,type,(
    k3_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_183,negated_conjecture,(
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
                    ( ( v1_funct_1(D)
                      & v1_funct_2(D,u1_struct_0(A),u1_struct_0(B))
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                   => r2_funct_2(u1_struct_0(C),u1_struct_0(B),k2_tmap_1(A,B,D,C),k1_partfun1(u1_struct_0(C),u1_struct_0(A),u1_struct_0(A),u1_struct_0(B),k4_tmap_1(A,C),D)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_tmap_1)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_28,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k3_struct_0(A) = k6_partfun1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_struct_0)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_93,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( r2_relset_1(A,B,k4_relset_1(A,A,A,B,k6_partfun1(A),C),C)
        & r2_relset_1(A,B,k4_relset_1(A,B,B,B,C,k6_partfun1(B)),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_2)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ( v1_funct_1(k3_struct_0(A))
        & v1_funct_2(k3_struct_0(A),u1_struct_0(A),u1_struct_0(A))
        & m1_subset_1(k3_struct_0(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_struct_0)).

tff(f_54,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(f_101,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_152,axiom,(
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
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,A) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(A),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                     => ! [F] :
                          ( ( v1_funct_1(F)
                            & v1_funct_2(F,u1_struct_0(B),u1_struct_0(C))
                            & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(C)))) )
                         => r2_funct_2(u1_struct_0(D),u1_struct_0(C),k2_tmap_1(A,C,k1_partfun1(u1_struct_0(A),u1_struct_0(B),u1_struct_0(B),u1_struct_0(C),E,F),D),k1_partfun1(u1_struct_0(D),u1_struct_0(B),u1_struct_0(B),u1_struct_0(C),k2_tmap_1(A,B,E,D),F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tmap_1)).

tff(f_40,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => k4_tmap_1(A,B) = k2_tmap_1(A,A,k3_struct_0(A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tmap_1)).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_48,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_60,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_58,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_54,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_52,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_24,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2,plain,(
    ! [A_1] :
      ( k6_partfun1(u1_struct_0(A_1)) = k3_struct_0(A_1)
      | ~ l1_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_22,plain,(
    ! [A_14] : m1_subset_1(k6_partfun1(A_14),k1_zfmisc_1(k2_zfmisc_1(A_14,A_14))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_172,plain,(
    ! [D_148,A_144,B_149,C_145,E_146,F_147] :
      ( k4_relset_1(A_144,B_149,C_145,D_148,E_146,F_147) = k5_relat_1(E_146,F_147)
      | ~ m1_subset_1(F_147,k1_zfmisc_1(k2_zfmisc_1(C_145,D_148)))
      | ~ m1_subset_1(E_146,k1_zfmisc_1(k2_zfmisc_1(A_144,B_149))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_185,plain,(
    ! [A_150,B_151,E_152] :
      ( k4_relset_1(A_150,B_151,u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),E_152,'#skF_4') = k5_relat_1(E_152,'#skF_4')
      | ~ m1_subset_1(E_152,k1_zfmisc_1(k2_zfmisc_1(A_150,B_151))) ) ),
    inference(resolution,[status(thm)],[c_42,c_172])).

tff(c_206,plain,(
    ! [A_153] : k4_relset_1(A_153,A_153,u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k6_partfun1(A_153),'#skF_4') = k5_relat_1(k6_partfun1(A_153),'#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_185])).

tff(c_36,plain,(
    ! [A_32,B_33,C_34] :
      ( r2_relset_1(A_32,B_33,k4_relset_1(A_32,A_32,A_32,B_33,k6_partfun1(A_32),C_34),C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_213,plain,
    ( r2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k5_relat_1(k6_partfun1(u1_struct_0('#skF_1')),'#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_36])).

tff(c_222,plain,(
    r2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k5_relat_1(k6_partfun1(u1_struct_0('#skF_1')),'#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_213])).

tff(c_237,plain,
    ( r2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k5_relat_1(k3_struct_0('#skF_1'),'#skF_4'),'#skF_4')
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_222])).

tff(c_241,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_237])).

tff(c_244,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_241])).

tff(c_248,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_244])).

tff(c_250,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_237])).

tff(c_10,plain,(
    ! [A_5] :
      ( v1_funct_1(k3_struct_0(A_5))
      | ~ l1_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_46,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_44,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_201,plain,(
    ! [A_14] : k4_relset_1(A_14,A_14,u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k6_partfun1(A_14),'#skF_4') = k5_relat_1(k6_partfun1(A_14),'#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_185])).

tff(c_256,plain,(
    ! [D_155,E_159,A_158,C_156,B_157,F_160] :
      ( m1_subset_1(k4_relset_1(A_158,B_157,C_156,D_155,E_159,F_160),k1_zfmisc_1(k2_zfmisc_1(A_158,D_155)))
      | ~ m1_subset_1(F_160,k1_zfmisc_1(k2_zfmisc_1(C_156,D_155)))
      | ~ m1_subset_1(E_159,k1_zfmisc_1(k2_zfmisc_1(A_158,B_157))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_269,plain,(
    ! [A_14] :
      ( m1_subset_1(k5_relat_1(k6_partfun1(A_14),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(A_14,u1_struct_0('#skF_2'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ m1_subset_1(k6_partfun1(A_14),k1_zfmisc_1(k2_zfmisc_1(A_14,A_14))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_256])).

tff(c_279,plain,(
    ! [A_14] : m1_subset_1(k5_relat_1(k6_partfun1(A_14),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(A_14,u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_42,c_269])).

tff(c_282,plain,(
    ! [A_161] : m1_subset_1(k5_relat_1(k6_partfun1(A_161),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(A_161,u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_42,c_269])).

tff(c_292,plain,(
    ! [A_1] :
      ( m1_subset_1(k5_relat_1(k3_struct_0(A_1),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1),u1_struct_0('#skF_2'))))
      | ~ l1_struct_0(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_282])).

tff(c_249,plain,(
    r2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k5_relat_1(k3_struct_0('#skF_1'),'#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_237])).

tff(c_32,plain,(
    ! [D_31,C_30,A_28,B_29] :
      ( D_31 = C_30
      | ~ r2_relset_1(A_28,B_29,C_30,D_31)
      | ~ m1_subset_1(D_31,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29)))
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_252,plain,
    ( k5_relat_1(k3_struct_0('#skF_1'),'#skF_4') = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ m1_subset_1(k5_relat_1(k3_struct_0('#skF_1'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(resolution,[status(thm)],[c_249,c_32])).

tff(c_255,plain,
    ( k5_relat_1(k3_struct_0('#skF_1'),'#skF_4') = '#skF_4'
    | ~ m1_subset_1(k5_relat_1(k3_struct_0('#skF_1'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_252])).

tff(c_396,plain,(
    ~ m1_subset_1(k5_relat_1(k3_struct_0('#skF_1'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_255])).

tff(c_399,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_292,c_396])).

tff(c_403,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_399])).

tff(c_404,plain,(
    k5_relat_1(k3_struct_0('#skF_1'),'#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_255])).

tff(c_30,plain,(
    ! [A_28,B_29,D_31] :
      ( r2_relset_1(A_28,B_29,D_31,D_31)
      | ~ m1_subset_1(D_31,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_321,plain,(
    ! [A_162] : r2_relset_1(A_162,u1_struct_0('#skF_2'),k5_relat_1(k6_partfun1(A_162),'#skF_4'),k5_relat_1(k6_partfun1(A_162),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_282,c_30])).

tff(c_495,plain,(
    ! [A_175] :
      ( r2_relset_1(u1_struct_0(A_175),u1_struct_0('#skF_2'),k5_relat_1(k3_struct_0(A_175),'#skF_4'),k5_relat_1(k6_partfun1(u1_struct_0(A_175)),'#skF_4'))
      | ~ l1_struct_0(A_175) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_321])).

tff(c_500,plain,
    ( r2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4',k5_relat_1(k6_partfun1(u1_struct_0('#skF_1')),'#skF_4'))
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_404,c_495])).

tff(c_508,plain,(
    r2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_4',k5_relat_1(k6_partfun1(u1_struct_0('#skF_1')),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_500])).

tff(c_514,plain,
    ( k5_relat_1(k6_partfun1(u1_struct_0('#skF_1')),'#skF_4') = '#skF_4'
    | ~ m1_subset_1(k5_relat_1(k6_partfun1(u1_struct_0('#skF_1')),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(resolution,[status(thm)],[c_508,c_32])).

tff(c_520,plain,(
    k5_relat_1(k6_partfun1(u1_struct_0('#skF_1')),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_279,c_514])).

tff(c_366,plain,(
    ! [B_166,C_170,D_169,E_167,F_165,A_168] :
      ( k1_partfun1(A_168,B_166,C_170,D_169,E_167,F_165) = k5_relat_1(E_167,F_165)
      | ~ m1_subset_1(F_165,k1_zfmisc_1(k2_zfmisc_1(C_170,D_169)))
      | ~ v1_funct_1(F_165)
      | ~ m1_subset_1(E_167,k1_zfmisc_1(k2_zfmisc_1(A_168,B_166)))
      | ~ v1_funct_1(E_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_382,plain,(
    ! [A_168,B_166,E_167] :
      ( k1_partfun1(A_168,B_166,u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),E_167,'#skF_4') = k5_relat_1(E_167,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_167,k1_zfmisc_1(k2_zfmisc_1(A_168,B_166)))
      | ~ v1_funct_1(E_167) ) ),
    inference(resolution,[status(thm)],[c_42,c_366])).

tff(c_587,plain,(
    ! [A_183,B_184,E_185] :
      ( k1_partfun1(A_183,B_184,u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),E_185,'#skF_4') = k5_relat_1(E_185,'#skF_4')
      | ~ m1_subset_1(E_185,k1_zfmisc_1(k2_zfmisc_1(A_183,B_184)))
      | ~ v1_funct_1(E_185) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_382])).

tff(c_638,plain,(
    ! [A_186] :
      ( k1_partfun1(A_186,A_186,u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k6_partfun1(A_186),'#skF_4') = k5_relat_1(k6_partfun1(A_186),'#skF_4')
      | ~ v1_funct_1(k6_partfun1(A_186)) ) ),
    inference(resolution,[status(thm)],[c_22,c_587])).

tff(c_38,plain,(
    ! [A_35,F_97,B_67,E_95,D_91,C_83] :
      ( r2_funct_2(u1_struct_0(D_91),u1_struct_0(C_83),k2_tmap_1(A_35,C_83,k1_partfun1(u1_struct_0(A_35),u1_struct_0(B_67),u1_struct_0(B_67),u1_struct_0(C_83),E_95,F_97),D_91),k1_partfun1(u1_struct_0(D_91),u1_struct_0(B_67),u1_struct_0(B_67),u1_struct_0(C_83),k2_tmap_1(A_35,B_67,E_95,D_91),F_97))
      | ~ m1_subset_1(F_97,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_67),u1_struct_0(C_83))))
      | ~ v1_funct_2(F_97,u1_struct_0(B_67),u1_struct_0(C_83))
      | ~ v1_funct_1(F_97)
      | ~ m1_subset_1(E_95,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_35),u1_struct_0(B_67))))
      | ~ v1_funct_2(E_95,u1_struct_0(A_35),u1_struct_0(B_67))
      | ~ v1_funct_1(E_95)
      | ~ m1_pre_topc(D_91,A_35)
      | v2_struct_0(D_91)
      | ~ l1_pre_topc(C_83)
      | ~ v2_pre_topc(C_83)
      | v2_struct_0(C_83)
      | ~ l1_pre_topc(B_67)
      | ~ v2_pre_topc(B_67)
      | v2_struct_0(B_67)
      | ~ l1_pre_topc(A_35)
      | ~ v2_pre_topc(A_35)
      | v2_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_645,plain,(
    ! [D_91] :
      ( r2_funct_2(u1_struct_0(D_91),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2',k5_relat_1(k6_partfun1(u1_struct_0('#skF_1')),'#skF_4'),D_91),k1_partfun1(u1_struct_0(D_91),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_1',k6_partfun1(u1_struct_0('#skF_1')),D_91),'#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_1')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_1')),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1(k6_partfun1(u1_struct_0('#skF_1')))
      | ~ m1_pre_topc(D_91,'#skF_1')
      | v2_struct_0(D_91)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ v1_funct_1(k6_partfun1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_638,c_38])).

tff(c_654,plain,(
    ! [D_91] :
      ( r2_funct_2(u1_struct_0(D_91),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_4',D_91),k1_partfun1(u1_struct_0(D_91),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_1',k6_partfun1(u1_struct_0('#skF_1')),D_91),'#skF_4'))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_1')),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'))
      | ~ m1_pre_topc(D_91,'#skF_1')
      | v2_struct_0(D_91)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1')
      | ~ v1_funct_1(k6_partfun1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_60,c_58,c_54,c_52,c_22,c_46,c_44,c_42,c_520,c_645])).

tff(c_655,plain,(
    ! [D_91] :
      ( r2_funct_2(u1_struct_0(D_91),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_4',D_91),k1_partfun1(u1_struct_0(D_91),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_1',k6_partfun1(u1_struct_0('#skF_1')),D_91),'#skF_4'))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_1')),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'))
      | ~ m1_pre_topc(D_91,'#skF_1')
      | v2_struct_0(D_91)
      | ~ v1_funct_1(k6_partfun1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_654])).

tff(c_903,plain,(
    ~ v1_funct_1(k6_partfun1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_655])).

tff(c_906,plain,
    ( ~ v1_funct_1(k3_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_903])).

tff(c_908,plain,(
    ~ v1_funct_1(k3_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_906])).

tff(c_911,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_908])).

tff(c_915,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_911])).

tff(c_917,plain,(
    v1_funct_1(k6_partfun1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_655])).

tff(c_922,plain,
    ( v1_funct_1(k3_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_917])).

tff(c_925,plain,(
    v1_funct_1(k3_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_922])).

tff(c_8,plain,(
    ! [A_5] :
      ( v1_funct_2(k3_struct_0(A_5),u1_struct_0(A_5),u1_struct_0(A_5))
      | ~ l1_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_6,plain,(
    ! [A_5] :
      ( m1_subset_1(k3_struct_0(A_5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_5),u1_struct_0(A_5))))
      | ~ l1_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_3843,plain,(
    ! [A_353] :
      ( k1_partfun1(u1_struct_0(A_353),u1_struct_0(A_353),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k3_struct_0(A_353),'#skF_4') = k5_relat_1(k3_struct_0(A_353),'#skF_4')
      | ~ v1_funct_1(k3_struct_0(A_353))
      | ~ l1_struct_0(A_353) ) ),
    inference(resolution,[status(thm)],[c_6,c_587])).

tff(c_4,plain,(
    ! [A_2,B_4] :
      ( k2_tmap_1(A_2,A_2,k3_struct_0(A_2),B_4) = k4_tmap_1(A_2,B_4)
      | ~ m1_pre_topc(B_4,A_2)
      | ~ l1_pre_topc(A_2)
      | ~ v2_pre_topc(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_509,plain,(
    ! [D_177,A_176,C_178,E_180,B_181,F_179] :
      ( r2_funct_2(u1_struct_0(D_177),u1_struct_0(C_178),k2_tmap_1(A_176,C_178,k1_partfun1(u1_struct_0(A_176),u1_struct_0(B_181),u1_struct_0(B_181),u1_struct_0(C_178),E_180,F_179),D_177),k1_partfun1(u1_struct_0(D_177),u1_struct_0(B_181),u1_struct_0(B_181),u1_struct_0(C_178),k2_tmap_1(A_176,B_181,E_180,D_177),F_179))
      | ~ m1_subset_1(F_179,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_181),u1_struct_0(C_178))))
      | ~ v1_funct_2(F_179,u1_struct_0(B_181),u1_struct_0(C_178))
      | ~ v1_funct_1(F_179)
      | ~ m1_subset_1(E_180,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_176),u1_struct_0(B_181))))
      | ~ v1_funct_2(E_180,u1_struct_0(A_176),u1_struct_0(B_181))
      | ~ v1_funct_1(E_180)
      | ~ m1_pre_topc(D_177,A_176)
      | v2_struct_0(D_177)
      | ~ l1_pre_topc(C_178)
      | ~ v2_pre_topc(C_178)
      | v2_struct_0(C_178)
      | ~ l1_pre_topc(B_181)
      | ~ v2_pre_topc(B_181)
      | v2_struct_0(B_181)
      | ~ l1_pre_topc(A_176)
      | ~ v2_pre_topc(A_176)
      | v2_struct_0(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_512,plain,(
    ! [B_4,C_178,A_2,F_179] :
      ( r2_funct_2(u1_struct_0(B_4),u1_struct_0(C_178),k2_tmap_1(A_2,C_178,k1_partfun1(u1_struct_0(A_2),u1_struct_0(A_2),u1_struct_0(A_2),u1_struct_0(C_178),k3_struct_0(A_2),F_179),B_4),k1_partfun1(u1_struct_0(B_4),u1_struct_0(A_2),u1_struct_0(A_2),u1_struct_0(C_178),k4_tmap_1(A_2,B_4),F_179))
      | ~ m1_subset_1(F_179,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2),u1_struct_0(C_178))))
      | ~ v1_funct_2(F_179,u1_struct_0(A_2),u1_struct_0(C_178))
      | ~ v1_funct_1(F_179)
      | ~ m1_subset_1(k3_struct_0(A_2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2),u1_struct_0(A_2))))
      | ~ v1_funct_2(k3_struct_0(A_2),u1_struct_0(A_2),u1_struct_0(A_2))
      | ~ v1_funct_1(k3_struct_0(A_2))
      | ~ m1_pre_topc(B_4,A_2)
      | v2_struct_0(B_4)
      | ~ l1_pre_topc(C_178)
      | ~ v2_pre_topc(C_178)
      | v2_struct_0(C_178)
      | ~ l1_pre_topc(A_2)
      | ~ v2_pre_topc(A_2)
      | v2_struct_0(A_2)
      | ~ l1_pre_topc(A_2)
      | ~ v2_pre_topc(A_2)
      | v2_struct_0(A_2)
      | ~ m1_pre_topc(B_4,A_2)
      | ~ l1_pre_topc(A_2)
      | ~ v2_pre_topc(A_2)
      | v2_struct_0(A_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_509])).

tff(c_3850,plain,(
    ! [B_4] :
      ( r2_funct_2(u1_struct_0(B_4),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2',k5_relat_1(k3_struct_0('#skF_1'),'#skF_4'),B_4),k1_partfun1(u1_struct_0(B_4),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_1',B_4),'#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(k3_struct_0('#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2(k3_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1(k3_struct_0('#skF_1'))
      | ~ m1_pre_topc(B_4,'#skF_1')
      | v2_struct_0(B_4)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ m1_pre_topc(B_4,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ v1_funct_1(k3_struct_0('#skF_1'))
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3843,c_512])).

tff(c_3860,plain,(
    ! [B_4] :
      ( r2_funct_2(u1_struct_0(B_4),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_4',B_4),k1_partfun1(u1_struct_0(B_4),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_1',B_4),'#skF_4'))
      | ~ m1_subset_1(k3_struct_0('#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2(k3_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'))
      | v2_struct_0(B_4)
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_4,'#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_925,c_60,c_58,c_60,c_58,c_60,c_58,c_54,c_52,c_925,c_46,c_44,c_42,c_404,c_3850])).

tff(c_3861,plain,(
    ! [B_4] :
      ( r2_funct_2(u1_struct_0(B_4),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_4',B_4),k1_partfun1(u1_struct_0(B_4),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_1',B_4),'#skF_4'))
      | ~ m1_subset_1(k3_struct_0('#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2(k3_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'))
      | v2_struct_0(B_4)
      | ~ m1_pre_topc(B_4,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_3860])).

tff(c_3889,plain,(
    ~ v1_funct_2(k3_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_3861])).

tff(c_3892,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_3889])).

tff(c_3896,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_3892])).

tff(c_3898,plain,(
    v1_funct_2(k3_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_3861])).

tff(c_3854,plain,(
    ! [D_91] :
      ( r2_funct_2(u1_struct_0(D_91),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2',k5_relat_1(k3_struct_0('#skF_1'),'#skF_4'),D_91),k1_partfun1(u1_struct_0(D_91),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_1',k3_struct_0('#skF_1'),D_91),'#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(k3_struct_0('#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2(k3_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1(k3_struct_0('#skF_1'))
      | ~ m1_pre_topc(D_91,'#skF_1')
      | v2_struct_0(D_91)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ v1_funct_1(k3_struct_0('#skF_1'))
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3843,c_38])).

tff(c_3863,plain,(
    ! [D_91] :
      ( r2_funct_2(u1_struct_0(D_91),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_4',D_91),k1_partfun1(u1_struct_0(D_91),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_1',k3_struct_0('#skF_1'),D_91),'#skF_4'))
      | ~ m1_subset_1(k3_struct_0('#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2(k3_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'))
      | ~ m1_pre_topc(D_91,'#skF_1')
      | v2_struct_0(D_91)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_925,c_60,c_58,c_60,c_58,c_54,c_52,c_925,c_46,c_44,c_42,c_404,c_3854])).

tff(c_3864,plain,(
    ! [D_91] :
      ( r2_funct_2(u1_struct_0(D_91),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_4',D_91),k1_partfun1(u1_struct_0(D_91),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_1',k3_struct_0('#skF_1'),D_91),'#skF_4'))
      | ~ m1_subset_1(k3_struct_0('#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2(k3_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'))
      | ~ m1_pre_topc(D_91,'#skF_1')
      | v2_struct_0(D_91) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_3863])).

tff(c_3979,plain,(
    ! [D_91] :
      ( r2_funct_2(u1_struct_0(D_91),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_4',D_91),k1_partfun1(u1_struct_0(D_91),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_1',k3_struct_0('#skF_1'),D_91),'#skF_4'))
      | ~ m1_subset_1(k3_struct_0('#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'))))
      | ~ m1_pre_topc(D_91,'#skF_1')
      | v2_struct_0(D_91) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3898,c_3864])).

tff(c_3980,plain,(
    ~ m1_subset_1(k3_struct_0('#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1')))) ),
    inference(splitLeft,[status(thm)],[c_3979])).

tff(c_3983,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_3980])).

tff(c_3987,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_3983])).

tff(c_3989,plain,(
    m1_subset_1(k3_struct_0('#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_3979])).

tff(c_394,plain,(
    ! [A_168,B_166,E_167] :
      ( k1_partfun1(A_168,B_166,u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),E_167,'#skF_4') = k5_relat_1(E_167,'#skF_4')
      | ~ m1_subset_1(E_167,k1_zfmisc_1(k2_zfmisc_1(A_168,B_166)))
      | ~ v1_funct_1(E_167) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_382])).

tff(c_4000,plain,
    ( k1_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k3_struct_0('#skF_1'),'#skF_4') = k5_relat_1(k3_struct_0('#skF_1'),'#skF_4')
    | ~ v1_funct_1(k3_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_3989,c_394])).

tff(c_4016,plain,(
    k1_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k3_struct_0('#skF_1'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_925,c_404,c_4000])).

tff(c_4036,plain,(
    ! [B_4] :
      ( r2_funct_2(u1_struct_0(B_4),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_4',B_4),k1_partfun1(u1_struct_0(B_4),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_1',B_4),'#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(k3_struct_0('#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2(k3_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1(k3_struct_0('#skF_1'))
      | ~ m1_pre_topc(B_4,'#skF_1')
      | v2_struct_0(B_4)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ m1_pre_topc(B_4,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4016,c_512])).

tff(c_4048,plain,(
    ! [B_4] :
      ( r2_funct_2(u1_struct_0(B_4),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_4',B_4),k1_partfun1(u1_struct_0(B_4),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_1',B_4),'#skF_4'))
      | v2_struct_0(B_4)
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_4,'#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_60,c_58,c_60,c_58,c_54,c_52,c_925,c_3898,c_3989,c_46,c_44,c_42,c_4036])).

tff(c_4759,plain,(
    ! [B_362] :
      ( r2_funct_2(u1_struct_0(B_362),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_4',B_362),k1_partfun1(u1_struct_0(B_362),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_1',B_362),'#skF_4'))
      | v2_struct_0(B_362)
      | ~ m1_pre_topc(B_362,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_4048])).

tff(c_40,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_1','#skF_3'),'#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_4762,plain,
    ( v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_4759,c_40])).

tff(c_4765,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_4762])).

tff(c_4767,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_4765])).

%------------------------------------------------------------------------------
