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
% DateTime   : Thu Dec  3 10:26:52 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.89s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 498 expanded)
%              Number of leaves         :   45 ( 184 expanded)
%              Depth                    :   19
%              Number of atoms          :  243 (1859 expanded)
%              Number of equality atoms :   37 ( 218 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(r1_funct_2,type,(
    r1_funct_2: ( $i * $i * $i * $i * $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

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
                  & m1_pre_topc(C,B) )
               => ! [D] :
                    ( ( v1_funct_1(D)
                      & v1_funct_2(D,u1_struct_0(B),u1_struct_0(A))
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
                   => ( g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                     => r1_funct_2(u1_struct_0(B),u1_struct_0(A),u1_struct_0(C),u1_struct_0(A),D,k2_tmap_1(B,A,D,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_tmap_1)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_98,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_129,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( ~ v1_xboole_0(B)
        & ~ v1_xboole_0(D)
        & v1_funct_1(E)
        & v1_funct_2(E,A,B)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & v1_funct_2(F,C,D)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( r1_funct_2(A,B,C,D,E,F)
      <=> E = F ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

tff(f_90,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_107,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_75,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_156,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(c_64,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_26,plain,(
    ! [A_21] :
      ( l1_struct_0(A_21)
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_52,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_80,plain,(
    ! [C_70,A_71,B_72] :
      ( v1_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_84,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_80])).

tff(c_96,plain,(
    ! [C_75,A_76,B_77] :
      ( v4_relat_1(C_75,A_76)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_100,plain,(
    v4_relat_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_48,c_96])).

tff(c_123,plain,(
    ! [B_86,A_87] :
      ( k1_relat_1(B_86) = A_87
      | ~ v1_partfun1(B_86,A_87)
      | ~ v4_relat_1(B_86,A_87)
      | ~ v1_relat_1(B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_126,plain,
    ( u1_struct_0('#skF_2') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',u1_struct_0('#skF_2'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_100,c_123])).

tff(c_129,plain,
    ( u1_struct_0('#skF_2') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_126])).

tff(c_130,plain,(
    ~ v1_partfun1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_129])).

tff(c_50,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_155,plain,(
    ! [C_100,A_101,B_102] :
      ( v1_partfun1(C_100,A_101)
      | ~ v1_funct_2(C_100,A_101,B_102)
      | ~ v1_funct_1(C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102)))
      | v1_xboole_0(B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_158,plain,
    ( v1_partfun1('#skF_4',u1_struct_0('#skF_2'))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_48,c_155])).

tff(c_161,plain,
    ( v1_partfun1('#skF_4',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_158])).

tff(c_162,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_161])).

tff(c_32,plain,(
    ! [A_26] :
      ( ~ v1_xboole_0(u1_struct_0(A_26))
      | ~ l1_struct_0(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_165,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_162,c_32])).

tff(c_168,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_165])).

tff(c_171,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_168])).

tff(c_175,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_171])).

tff(c_176,plain,(
    u1_struct_0('#skF_2') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_129])).

tff(c_182,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_50])).

tff(c_181,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_48])).

tff(c_353,plain,(
    ! [C_128,D_130,F_129,A_127,B_131] :
      ( r1_funct_2(A_127,B_131,C_128,D_130,F_129,F_129)
      | ~ m1_subset_1(F_129,k1_zfmisc_1(k2_zfmisc_1(C_128,D_130)))
      | ~ v1_funct_2(F_129,C_128,D_130)
      | ~ m1_subset_1(F_129,k1_zfmisc_1(k2_zfmisc_1(A_127,B_131)))
      | ~ v1_funct_2(F_129,A_127,B_131)
      | ~ v1_funct_1(F_129)
      | v1_xboole_0(D_130)
      | v1_xboole_0(B_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_355,plain,(
    ! [A_127,B_131] :
      ( r1_funct_2(A_127,B_131,k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_1'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_127,B_131)))
      | ~ v1_funct_2('#skF_4',A_127,B_131)
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_131) ) ),
    inference(resolution,[status(thm)],[c_181,c_353])).

tff(c_358,plain,(
    ! [A_127,B_131] :
      ( r1_funct_2(A_127,B_131,k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_127,B_131)))
      | ~ v1_funct_2('#skF_4',A_127,B_131)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_182,c_355])).

tff(c_366,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_358])).

tff(c_369,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_366,c_32])).

tff(c_372,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_369])).

tff(c_375,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_372])).

tff(c_379,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_375])).

tff(c_381,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_358])).

tff(c_380,plain,(
    ! [A_127,B_131] :
      ( r1_funct_2(A_127,B_131,k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_127,B_131)))
      | ~ v1_funct_2('#skF_4',A_127,B_131)
      | v1_xboole_0(B_131) ) ),
    inference(splitRight,[status(thm)],[c_358])).

tff(c_54,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_58,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_30,plain,(
    ! [A_25] :
      ( m1_subset_1(u1_pre_topc(A_25),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_25))))
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_186,plain,
    ( m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(k1_relat_1('#skF_4'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_30])).

tff(c_193,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(k1_relat_1('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_186])).

tff(c_46,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_180,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_46])).

tff(c_36,plain,(
    ! [C_31,A_27,D_32,B_28] :
      ( C_31 = A_27
      | g1_pre_topc(C_31,D_32) != g1_pre_topc(A_27,B_28)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(k1_zfmisc_1(A_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_280,plain,(
    ! [A_119,B_120] :
      ( u1_struct_0('#skF_3') = A_119
      | g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2')) != g1_pre_topc(A_119,B_120)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(k1_zfmisc_1(A_119))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_36])).

tff(c_287,plain,(
    u1_struct_0('#skF_3') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_193,c_280])).

tff(c_66,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_258,plain,(
    ! [A_111,B_112,C_113,D_114] :
      ( k2_partfun1(A_111,B_112,C_113,D_114) = k7_relat_1(C_113,D_114)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112)))
      | ~ v1_funct_1(C_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_260,plain,(
    ! [D_114] :
      ( k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4',D_114) = k7_relat_1('#skF_4',D_114)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_181,c_258])).

tff(c_263,plain,(
    ! [D_114] : k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4',D_114) = k7_relat_1('#skF_4',D_114) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_260])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_60,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_391,plain,(
    ! [A_140,B_141,C_142,D_143] :
      ( k2_partfun1(u1_struct_0(A_140),u1_struct_0(B_141),C_142,u1_struct_0(D_143)) = k2_tmap_1(A_140,B_141,C_142,D_143)
      | ~ m1_pre_topc(D_143,A_140)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_140),u1_struct_0(B_141))))
      | ~ v1_funct_2(C_142,u1_struct_0(A_140),u1_struct_0(B_141))
      | ~ v1_funct_1(C_142)
      | ~ l1_pre_topc(B_141)
      | ~ v2_pre_topc(B_141)
      | v2_struct_0(B_141)
      | ~ l1_pre_topc(A_140)
      | ~ v2_pre_topc(A_140)
      | v2_struct_0(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_397,plain,(
    ! [B_141,C_142,D_143] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0(B_141),C_142,u1_struct_0(D_143)) = k2_tmap_1('#skF_2',B_141,C_142,D_143)
      | ~ m1_pre_topc(D_143,'#skF_2')
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_141))))
      | ~ v1_funct_2(C_142,u1_struct_0('#skF_2'),u1_struct_0(B_141))
      | ~ v1_funct_1(C_142)
      | ~ l1_pre_topc(B_141)
      | ~ v2_pre_topc(B_141)
      | v2_struct_0(B_141)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_391])).

tff(c_407,plain,(
    ! [B_141,C_142,D_143] :
      ( k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0(B_141),C_142,u1_struct_0(D_143)) = k2_tmap_1('#skF_2',B_141,C_142,D_143)
      | ~ m1_pre_topc(D_143,'#skF_2')
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_141))))
      | ~ v1_funct_2(C_142,k1_relat_1('#skF_4'),u1_struct_0(B_141))
      | ~ v1_funct_1(C_142)
      | ~ l1_pre_topc(B_141)
      | ~ v2_pre_topc(B_141)
      | v2_struct_0(B_141)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_176,c_176,c_397])).

tff(c_412,plain,(
    ! [B_144,C_145,D_146] :
      ( k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0(B_144),C_145,u1_struct_0(D_146)) = k2_tmap_1('#skF_2',B_144,C_145,D_146)
      | ~ m1_pre_topc(D_146,'#skF_2')
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_144))))
      | ~ v1_funct_2(C_145,k1_relat_1('#skF_4'),u1_struct_0(B_144))
      | ~ v1_funct_1(C_145)
      | ~ l1_pre_topc(B_144)
      | ~ v2_pre_topc(B_144)
      | v2_struct_0(B_144) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_407])).

tff(c_416,plain,(
    ! [D_146] :
      ( k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_146)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_146)
      | ~ m1_pre_topc(D_146,'#skF_2')
      | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_181,c_412])).

tff(c_424,plain,(
    ! [D_146] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_146)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_146)
      | ~ m1_pre_topc(D_146,'#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_52,c_182,c_263,c_416])).

tff(c_429,plain,(
    ! [D_147] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_147)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_147)
      | ~ m1_pre_topc(D_147,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_424])).

tff(c_438,plain,
    ( k7_relat_1('#skF_4',k1_relat_1('#skF_4')) = k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_429])).

tff(c_445,plain,(
    k7_relat_1('#skF_4',k1_relat_1('#skF_4')) = k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_438])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_107,plain,(
    ! [B_82,A_83] :
      ( k7_relat_1(B_82,A_83) = B_82
      | ~ r1_tarski(k1_relat_1(B_82),A_83)
      | ~ v1_relat_1(B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_112,plain,(
    ! [B_82] :
      ( k7_relat_1(B_82,k1_relat_1(B_82)) = B_82
      | ~ v1_relat_1(B_82) ) ),
    inference(resolution,[status(thm)],[c_6,c_107])).

tff(c_449,plain,
    ( k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_445,c_112])).

tff(c_456,plain,(
    k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_449])).

tff(c_44,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_178,plain,(
    ~ r1_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_44])).

tff(c_290,plain,(
    ~ r1_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_287,c_178])).

tff(c_461,plain,(
    ~ r1_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_456,c_290])).

tff(c_485,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'))))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_380,c_461])).

tff(c_488,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_181,c_485])).

tff(c_490,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_381,c_488])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n002.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 16:22:36 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.71/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.37  
% 2.89/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.37  %$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.89/1.37  
% 2.89/1.37  %Foreground sorts:
% 2.89/1.37  
% 2.89/1.37  
% 2.89/1.37  %Background operators:
% 2.89/1.37  
% 2.89/1.37  
% 2.89/1.37  %Foreground operators:
% 2.89/1.37  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.89/1.37  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.89/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.89/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.89/1.37  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 2.89/1.37  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.89/1.37  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.89/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.89/1.37  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.89/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.89/1.37  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.89/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.89/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.89/1.37  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.89/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.89/1.37  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.89/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.89/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.89/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.89/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.89/1.37  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 2.89/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.89/1.37  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.89/1.37  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.89/1.37  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.89/1.37  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.89/1.37  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 2.89/1.37  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.89/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.89/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.89/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.89/1.37  
% 2.89/1.39  tff(f_189, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => r1_funct_2(u1_struct_0(B), u1_struct_0(A), u1_struct_0(C), u1_struct_0(A), D, k2_tmap_1(B, A, D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_tmap_1)).
% 2.89/1.39  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.89/1.39  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.89/1.39  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.89/1.39  tff(f_69, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 2.89/1.39  tff(f_61, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.89/1.39  tff(f_98, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.89/1.39  tff(f_129, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (r1_funct_2(A, B, C, D, E, F) <=> (E = F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 2.89/1.39  tff(f_90, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 2.89/1.39  tff(f_107, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 2.89/1.39  tff(f_75, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.89/1.39  tff(f_156, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 2.89/1.39  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.89/1.39  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 2.89/1.39  tff(c_64, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_189])).
% 2.89/1.39  tff(c_26, plain, (![A_21]: (l1_struct_0(A_21) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.89/1.39  tff(c_68, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_189])).
% 2.89/1.39  tff(c_52, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_189])).
% 2.89/1.39  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_189])).
% 2.89/1.39  tff(c_80, plain, (![C_70, A_71, B_72]: (v1_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.89/1.39  tff(c_84, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_80])).
% 2.89/1.39  tff(c_96, plain, (![C_75, A_76, B_77]: (v4_relat_1(C_75, A_76) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.89/1.39  tff(c_100, plain, (v4_relat_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_48, c_96])).
% 2.89/1.39  tff(c_123, plain, (![B_86, A_87]: (k1_relat_1(B_86)=A_87 | ~v1_partfun1(B_86, A_87) | ~v4_relat_1(B_86, A_87) | ~v1_relat_1(B_86))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.89/1.39  tff(c_126, plain, (u1_struct_0('#skF_2')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', u1_struct_0('#skF_2')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_100, c_123])).
% 2.89/1.39  tff(c_129, plain, (u1_struct_0('#skF_2')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_126])).
% 2.89/1.39  tff(c_130, plain, (~v1_partfun1('#skF_4', u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_129])).
% 2.89/1.39  tff(c_50, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_189])).
% 2.89/1.39  tff(c_155, plain, (![C_100, A_101, B_102]: (v1_partfun1(C_100, A_101) | ~v1_funct_2(C_100, A_101, B_102) | ~v1_funct_1(C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))) | v1_xboole_0(B_102))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.89/1.39  tff(c_158, plain, (v1_partfun1('#skF_4', u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_155])).
% 2.89/1.39  tff(c_161, plain, (v1_partfun1('#skF_4', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_158])).
% 2.89/1.39  tff(c_162, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_130, c_161])).
% 2.89/1.39  tff(c_32, plain, (![A_26]: (~v1_xboole_0(u1_struct_0(A_26)) | ~l1_struct_0(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.89/1.39  tff(c_165, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_162, c_32])).
% 2.89/1.39  tff(c_168, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_68, c_165])).
% 2.89/1.39  tff(c_171, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_168])).
% 2.89/1.39  tff(c_175, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_171])).
% 2.89/1.39  tff(c_176, plain, (u1_struct_0('#skF_2')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_129])).
% 2.89/1.39  tff(c_182, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_176, c_50])).
% 2.89/1.39  tff(c_181, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_176, c_48])).
% 2.89/1.39  tff(c_353, plain, (![C_128, D_130, F_129, A_127, B_131]: (r1_funct_2(A_127, B_131, C_128, D_130, F_129, F_129) | ~m1_subset_1(F_129, k1_zfmisc_1(k2_zfmisc_1(C_128, D_130))) | ~v1_funct_2(F_129, C_128, D_130) | ~m1_subset_1(F_129, k1_zfmisc_1(k2_zfmisc_1(A_127, B_131))) | ~v1_funct_2(F_129, A_127, B_131) | ~v1_funct_1(F_129) | v1_xboole_0(D_130) | v1_xboole_0(B_131))), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.89/1.39  tff(c_355, plain, (![A_127, B_131]: (r1_funct_2(A_127, B_131, k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_127, B_131))) | ~v1_funct_2('#skF_4', A_127, B_131) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_131))), inference(resolution, [status(thm)], [c_181, c_353])).
% 2.89/1.39  tff(c_358, plain, (![A_127, B_131]: (r1_funct_2(A_127, B_131, k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_127, B_131))) | ~v1_funct_2('#skF_4', A_127, B_131) | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_131))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_182, c_355])).
% 2.89/1.39  tff(c_366, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_358])).
% 2.89/1.39  tff(c_369, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_366, c_32])).
% 2.89/1.39  tff(c_372, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_68, c_369])).
% 2.89/1.39  tff(c_375, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_372])).
% 2.89/1.39  tff(c_379, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_375])).
% 2.89/1.39  tff(c_381, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_358])).
% 2.89/1.39  tff(c_380, plain, (![A_127, B_131]: (r1_funct_2(A_127, B_131, k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_127, B_131))) | ~v1_funct_2('#skF_4', A_127, B_131) | v1_xboole_0(B_131))), inference(splitRight, [status(thm)], [c_358])).
% 2.89/1.39  tff(c_54, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_189])).
% 2.89/1.39  tff(c_58, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_189])).
% 2.89/1.39  tff(c_30, plain, (![A_25]: (m1_subset_1(u1_pre_topc(A_25), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_25)))) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.89/1.39  tff(c_186, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(k1_relat_1('#skF_4')))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_176, c_30])).
% 2.89/1.39  tff(c_193, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(k1_relat_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_186])).
% 2.89/1.39  tff(c_46, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_189])).
% 2.89/1.39  tff(c_180, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_176, c_46])).
% 2.89/1.39  tff(c_36, plain, (![C_31, A_27, D_32, B_28]: (C_31=A_27 | g1_pre_topc(C_31, D_32)!=g1_pre_topc(A_27, B_28) | ~m1_subset_1(B_28, k1_zfmisc_1(k1_zfmisc_1(A_27))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.89/1.39  tff(c_280, plain, (![A_119, B_120]: (u1_struct_0('#skF_3')=A_119 | g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2'))!=g1_pre_topc(A_119, B_120) | ~m1_subset_1(B_120, k1_zfmisc_1(k1_zfmisc_1(A_119))))), inference(superposition, [status(thm), theory('equality')], [c_180, c_36])).
% 2.89/1.39  tff(c_287, plain, (u1_struct_0('#skF_3')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_193, c_280])).
% 2.89/1.39  tff(c_66, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_189])).
% 2.89/1.39  tff(c_258, plain, (![A_111, B_112, C_113, D_114]: (k2_partfun1(A_111, B_112, C_113, D_114)=k7_relat_1(C_113, D_114) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))) | ~v1_funct_1(C_113))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.89/1.39  tff(c_260, plain, (![D_114]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', D_114)=k7_relat_1('#skF_4', D_114) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_181, c_258])).
% 2.89/1.39  tff(c_263, plain, (![D_114]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', D_114)=k7_relat_1('#skF_4', D_114))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_260])).
% 2.89/1.39  tff(c_62, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_189])).
% 2.89/1.39  tff(c_60, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_189])).
% 2.89/1.39  tff(c_391, plain, (![A_140, B_141, C_142, D_143]: (k2_partfun1(u1_struct_0(A_140), u1_struct_0(B_141), C_142, u1_struct_0(D_143))=k2_tmap_1(A_140, B_141, C_142, D_143) | ~m1_pre_topc(D_143, A_140) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_140), u1_struct_0(B_141)))) | ~v1_funct_2(C_142, u1_struct_0(A_140), u1_struct_0(B_141)) | ~v1_funct_1(C_142) | ~l1_pre_topc(B_141) | ~v2_pre_topc(B_141) | v2_struct_0(B_141) | ~l1_pre_topc(A_140) | ~v2_pre_topc(A_140) | v2_struct_0(A_140))), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.89/1.39  tff(c_397, plain, (![B_141, C_142, D_143]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0(B_141), C_142, u1_struct_0(D_143))=k2_tmap_1('#skF_2', B_141, C_142, D_143) | ~m1_pre_topc(D_143, '#skF_2') | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_141)))) | ~v1_funct_2(C_142, u1_struct_0('#skF_2'), u1_struct_0(B_141)) | ~v1_funct_1(C_142) | ~l1_pre_topc(B_141) | ~v2_pre_topc(B_141) | v2_struct_0(B_141) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_176, c_391])).
% 2.89/1.39  tff(c_407, plain, (![B_141, C_142, D_143]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0(B_141), C_142, u1_struct_0(D_143))=k2_tmap_1('#skF_2', B_141, C_142, D_143) | ~m1_pre_topc(D_143, '#skF_2') | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_141)))) | ~v1_funct_2(C_142, k1_relat_1('#skF_4'), u1_struct_0(B_141)) | ~v1_funct_1(C_142) | ~l1_pre_topc(B_141) | ~v2_pre_topc(B_141) | v2_struct_0(B_141) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_176, c_176, c_397])).
% 2.89/1.39  tff(c_412, plain, (![B_144, C_145, D_146]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0(B_144), C_145, u1_struct_0(D_146))=k2_tmap_1('#skF_2', B_144, C_145, D_146) | ~m1_pre_topc(D_146, '#skF_2') | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_144)))) | ~v1_funct_2(C_145, k1_relat_1('#skF_4'), u1_struct_0(B_144)) | ~v1_funct_1(C_145) | ~l1_pre_topc(B_144) | ~v2_pre_topc(B_144) | v2_struct_0(B_144))), inference(negUnitSimplification, [status(thm)], [c_62, c_407])).
% 2.89/1.39  tff(c_416, plain, (![D_146]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_146))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_146) | ~m1_pre_topc(D_146, '#skF_2') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_181, c_412])).
% 2.89/1.39  tff(c_424, plain, (![D_146]: (k7_relat_1('#skF_4', u1_struct_0(D_146))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_146) | ~m1_pre_topc(D_146, '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_52, c_182, c_263, c_416])).
% 2.89/1.39  tff(c_429, plain, (![D_147]: (k7_relat_1('#skF_4', u1_struct_0(D_147))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_147) | ~m1_pre_topc(D_147, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_68, c_424])).
% 2.89/1.39  tff(c_438, plain, (k7_relat_1('#skF_4', k1_relat_1('#skF_4'))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_287, c_429])).
% 2.89/1.39  tff(c_445, plain, (k7_relat_1('#skF_4', k1_relat_1('#skF_4'))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_438])).
% 2.89/1.39  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.89/1.39  tff(c_107, plain, (![B_82, A_83]: (k7_relat_1(B_82, A_83)=B_82 | ~r1_tarski(k1_relat_1(B_82), A_83) | ~v1_relat_1(B_82))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.89/1.39  tff(c_112, plain, (![B_82]: (k7_relat_1(B_82, k1_relat_1(B_82))=B_82 | ~v1_relat_1(B_82))), inference(resolution, [status(thm)], [c_6, c_107])).
% 2.89/1.39  tff(c_449, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_445, c_112])).
% 2.89/1.39  tff(c_456, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_449])).
% 2.89/1.39  tff(c_44, plain, (~r1_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_189])).
% 2.89/1.39  tff(c_178, plain, (~r1_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_176, c_44])).
% 2.89/1.39  tff(c_290, plain, (~r1_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_287, c_178])).
% 2.89/1.39  tff(c_461, plain, (~r1_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_456, c_290])).
% 2.89/1.39  tff(c_485, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_380, c_461])).
% 2.89/1.39  tff(c_488, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_181, c_485])).
% 2.89/1.39  tff(c_490, plain, $false, inference(negUnitSimplification, [status(thm)], [c_381, c_488])).
% 2.89/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.39  
% 2.89/1.39  Inference rules
% 2.89/1.39  ----------------------
% 2.89/1.39  #Ref     : 7
% 2.89/1.39  #Sup     : 81
% 2.89/1.39  #Fact    : 0
% 2.89/1.39  #Define  : 0
% 2.89/1.39  #Split   : 3
% 2.89/1.39  #Chain   : 0
% 2.89/1.39  #Close   : 0
% 2.89/1.39  
% 2.89/1.39  Ordering : KBO
% 2.89/1.39  
% 2.89/1.39  Simplification rules
% 2.89/1.39  ----------------------
% 2.89/1.39  #Subsume      : 8
% 2.89/1.39  #Demod        : 92
% 2.89/1.39  #Tautology    : 47
% 2.89/1.39  #SimpNegUnit  : 14
% 2.89/1.39  #BackRed      : 12
% 2.89/1.39  
% 2.89/1.39  #Partial instantiations: 0
% 2.89/1.39  #Strategies tried      : 1
% 2.89/1.39  
% 2.89/1.39  Timing (in seconds)
% 2.89/1.39  ----------------------
% 2.89/1.39  Preprocessing        : 0.36
% 2.89/1.39  Parsing              : 0.19
% 2.89/1.39  CNF conversion       : 0.03
% 2.89/1.40  Main loop            : 0.28
% 2.89/1.40  Inferencing          : 0.09
% 2.89/1.40  Reduction            : 0.10
% 2.89/1.40  Demodulation         : 0.07
% 2.89/1.40  BG Simplification    : 0.02
% 2.89/1.40  Subsumption          : 0.04
% 2.89/1.40  Abstraction          : 0.01
% 2.89/1.40  MUC search           : 0.00
% 2.89/1.40  Cooper               : 0.00
% 2.89/1.40  Total                : 0.67
% 2.89/1.40  Index Insertion      : 0.00
% 2.89/1.40  Index Deletion       : 0.00
% 2.89/1.40  Index Matching       : 0.00
% 2.89/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
