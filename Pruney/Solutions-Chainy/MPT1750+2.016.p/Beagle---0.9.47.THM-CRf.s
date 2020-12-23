%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:53 EST 2020

% Result     : Theorem 2.92s
% Output     : CNFRefutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 670 expanded)
%              Number of leaves         :   43 ( 238 expanded)
%              Depth                    :   19
%              Number of atoms          :  246 (2471 expanded)
%              Number of equality atoms :   42 ( 324 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_174,negated_conjecture,(
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

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_83,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_114,axiom,(
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

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_92,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_141,axiom,(
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

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(c_56,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_20,plain,(
    ! [A_18] :
      ( l1_struct_0(A_18)
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_44,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_72,plain,(
    ! [C_62,A_63,B_64] :
      ( v1_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_76,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_72])).

tff(c_77,plain,(
    ! [C_65,A_66,B_67] :
      ( v4_relat_1(C_65,A_66)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_81,plain,(
    v4_relat_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_77])).

tff(c_93,plain,(
    ! [B_73,A_74] :
      ( k1_relat_1(B_73) = A_74
      | ~ v1_partfun1(B_73,A_74)
      | ~ v4_relat_1(B_73,A_74)
      | ~ v1_relat_1(B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_96,plain,
    ( u1_struct_0('#skF_2') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',u1_struct_0('#skF_2'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_81,c_93])).

tff(c_99,plain,
    ( u1_struct_0('#skF_2') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_96])).

tff(c_100,plain,(
    ~ v1_partfun1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_99])).

tff(c_42,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_156,plain,(
    ! [C_93,A_94,B_95] :
      ( v1_partfun1(C_93,A_94)
      | ~ v1_funct_2(C_93,A_94,B_95)
      | ~ v1_funct_1(C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95)))
      | v1_xboole_0(B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_159,plain,
    ( v1_partfun1('#skF_4',u1_struct_0('#skF_2'))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_40,c_156])).

tff(c_162,plain,
    ( v1_partfun1('#skF_4',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_159])).

tff(c_163,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_162])).

tff(c_24,plain,(
    ! [A_20] :
      ( ~ v1_xboole_0(u1_struct_0(A_20))
      | ~ l1_struct_0(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_166,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_163,c_24])).

tff(c_169,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_166])).

tff(c_172,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_169])).

tff(c_176,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_172])).

tff(c_177,plain,(
    u1_struct_0('#skF_2') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_183,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_42])).

tff(c_182,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_40])).

tff(c_339,plain,(
    ! [B_119,F_116,A_120,D_118,C_117] :
      ( r1_funct_2(A_120,B_119,C_117,D_118,F_116,F_116)
      | ~ m1_subset_1(F_116,k1_zfmisc_1(k2_zfmisc_1(C_117,D_118)))
      | ~ v1_funct_2(F_116,C_117,D_118)
      | ~ m1_subset_1(F_116,k1_zfmisc_1(k2_zfmisc_1(A_120,B_119)))
      | ~ v1_funct_2(F_116,A_120,B_119)
      | ~ v1_funct_1(F_116)
      | v1_xboole_0(D_118)
      | v1_xboole_0(B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_341,plain,(
    ! [A_120,B_119] :
      ( r1_funct_2(A_120,B_119,k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_1'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_120,B_119)))
      | ~ v1_funct_2('#skF_4',A_120,B_119)
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_119) ) ),
    inference(resolution,[status(thm)],[c_182,c_339])).

tff(c_344,plain,(
    ! [A_120,B_119] :
      ( r1_funct_2(A_120,B_119,k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_120,B_119)))
      | ~ v1_funct_2('#skF_4',A_120,B_119)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_119) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_183,c_341])).

tff(c_398,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_344])).

tff(c_401,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_398,c_24])).

tff(c_404,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_401])).

tff(c_408,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_404])).

tff(c_412,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_408])).

tff(c_414,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_344])).

tff(c_413,plain,(
    ! [A_120,B_119] :
      ( r1_funct_2(A_120,B_119,k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_120,B_119)))
      | ~ v1_funct_2('#skF_4',A_120,B_119)
      | v1_xboole_0(B_119) ) ),
    inference(splitRight,[status(thm)],[c_344])).

tff(c_46,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_50,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_22,plain,(
    ! [A_19] :
      ( m1_subset_1(u1_pre_topc(A_19),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_19))))
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_187,plain,
    ( m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(k1_relat_1('#skF_4'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_22])).

tff(c_194,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(k1_relat_1('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_187])).

tff(c_38,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_180,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_38])).

tff(c_26,plain,(
    ! [D_26,B_22,C_25,A_21] :
      ( D_26 = B_22
      | g1_pre_topc(C_25,D_26) != g1_pre_topc(A_21,B_22)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(k1_zfmisc_1(A_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_280,plain,(
    ! [B_112,A_113] :
      ( u1_pre_topc('#skF_3') = B_112
      | g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2')) != g1_pre_topc(A_113,B_112)
      | ~ m1_subset_1(B_112,k1_zfmisc_1(k1_zfmisc_1(A_113))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_26])).

tff(c_287,plain,(
    u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_194,c_280])).

tff(c_291,plain,(
    m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(k1_relat_1('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_287,c_194])).

tff(c_253,plain,(
    ! [C_100,A_101,D_102,B_103] :
      ( C_100 = A_101
      | g1_pre_topc(C_100,D_102) != g1_pre_topc(A_101,B_103)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(k1_zfmisc_1(A_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_255,plain,(
    ! [A_101,B_103] :
      ( u1_struct_0('#skF_3') = A_101
      | g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2')) != g1_pre_topc(A_101,B_103)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(k1_zfmisc_1(A_101))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_253])).

tff(c_315,plain,(
    ! [A_114,B_115] :
      ( u1_struct_0('#skF_3') = A_114
      | g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_3')) != g1_pre_topc(A_114,B_115)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(k1_zfmisc_1(A_114))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_287,c_255])).

tff(c_322,plain,(
    u1_struct_0('#skF_3') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_291,c_315])).

tff(c_58,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_258,plain,(
    ! [A_104,B_105,C_106,D_107] :
      ( k2_partfun1(A_104,B_105,C_106,D_107) = k7_relat_1(C_106,D_107)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105)))
      | ~ v1_funct_1(C_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_260,plain,(
    ! [D_107] :
      ( k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4',D_107) = k7_relat_1('#skF_4',D_107)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_182,c_258])).

tff(c_263,plain,(
    ! [D_107] : k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4',D_107) = k7_relat_1('#skF_4',D_107) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_260])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_52,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_424,plain,(
    ! [A_141,B_142,C_143,D_144] :
      ( k2_partfun1(u1_struct_0(A_141),u1_struct_0(B_142),C_143,u1_struct_0(D_144)) = k2_tmap_1(A_141,B_142,C_143,D_144)
      | ~ m1_pre_topc(D_144,A_141)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_141),u1_struct_0(B_142))))
      | ~ v1_funct_2(C_143,u1_struct_0(A_141),u1_struct_0(B_142))
      | ~ v1_funct_1(C_143)
      | ~ l1_pre_topc(B_142)
      | ~ v2_pre_topc(B_142)
      | v2_struct_0(B_142)
      | ~ l1_pre_topc(A_141)
      | ~ v2_pre_topc(A_141)
      | v2_struct_0(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_430,plain,(
    ! [B_142,C_143,D_144] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0(B_142),C_143,u1_struct_0(D_144)) = k2_tmap_1('#skF_2',B_142,C_143,D_144)
      | ~ m1_pre_topc(D_144,'#skF_2')
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_142))))
      | ~ v1_funct_2(C_143,u1_struct_0('#skF_2'),u1_struct_0(B_142))
      | ~ v1_funct_1(C_143)
      | ~ l1_pre_topc(B_142)
      | ~ v2_pre_topc(B_142)
      | v2_struct_0(B_142)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_424])).

tff(c_438,plain,(
    ! [B_142,C_143,D_144] :
      ( k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0(B_142),C_143,u1_struct_0(D_144)) = k2_tmap_1('#skF_2',B_142,C_143,D_144)
      | ~ m1_pre_topc(D_144,'#skF_2')
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_142))))
      | ~ v1_funct_2(C_143,k1_relat_1('#skF_4'),u1_struct_0(B_142))
      | ~ v1_funct_1(C_143)
      | ~ l1_pre_topc(B_142)
      | ~ v2_pre_topc(B_142)
      | v2_struct_0(B_142)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_177,c_177,c_430])).

tff(c_443,plain,(
    ! [B_145,C_146,D_147] :
      ( k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0(B_145),C_146,u1_struct_0(D_147)) = k2_tmap_1('#skF_2',B_145,C_146,D_147)
      | ~ m1_pre_topc(D_147,'#skF_2')
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_145))))
      | ~ v1_funct_2(C_146,k1_relat_1('#skF_4'),u1_struct_0(B_145))
      | ~ v1_funct_1(C_146)
      | ~ l1_pre_topc(B_145)
      | ~ v2_pre_topc(B_145)
      | v2_struct_0(B_145) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_438])).

tff(c_447,plain,(
    ! [D_147] :
      ( k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_147)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_147)
      | ~ m1_pre_topc(D_147,'#skF_2')
      | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_182,c_443])).

tff(c_454,plain,(
    ! [D_147] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_147)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_147)
      | ~ m1_pre_topc(D_147,'#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_44,c_183,c_263,c_447])).

tff(c_459,plain,(
    ! [D_148] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_148)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_148)
      | ~ m1_pre_topc(D_148,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_454])).

tff(c_468,plain,
    ( k7_relat_1('#skF_4',k1_relat_1('#skF_4')) = k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_322,c_459])).

tff(c_475,plain,(
    k7_relat_1('#skF_4',k1_relat_1('#skF_4')) = k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_468])).

tff(c_2,plain,(
    ! [A_1] :
      ( k7_relat_1(A_1,k1_relat_1(A_1)) = A_1
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_479,plain,
    ( k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_475,c_2])).

tff(c_486,plain,(
    k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_479])).

tff(c_36,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_179,plain,(
    ~ r1_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_36])).

tff(c_326,plain,(
    ~ r1_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_179])).

tff(c_491,plain,(
    ~ r1_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_486,c_326])).

tff(c_525,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'))))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_413,c_491])).

tff(c_528,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_182,c_525])).

tff(c_530,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_414,c_528])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:07:41 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.92/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.92/1.46  
% 2.92/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.92/1.46  %$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.92/1.46  
% 2.92/1.46  %Foreground sorts:
% 2.92/1.46  
% 2.92/1.46  
% 2.92/1.46  %Background operators:
% 2.92/1.46  
% 2.92/1.46  
% 2.92/1.46  %Foreground operators:
% 2.92/1.46  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.92/1.46  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.92/1.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.92/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.92/1.46  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 2.92/1.46  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.92/1.46  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.92/1.46  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.92/1.46  tff('#skF_2', type, '#skF_2': $i).
% 2.92/1.46  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.92/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.92/1.46  tff('#skF_1', type, '#skF_1': $i).
% 2.92/1.46  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.92/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.92/1.46  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.92/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.92/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.92/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.92/1.46  tff('#skF_4', type, '#skF_4': $i).
% 2.92/1.46  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 2.92/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.92/1.46  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.92/1.46  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.92/1.46  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.92/1.46  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.92/1.46  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 2.92/1.46  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.92/1.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.92/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.92/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.92/1.46  
% 3.25/1.48  tff(f_174, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => r1_funct_2(u1_struct_0(B), u1_struct_0(A), u1_struct_0(C), u1_struct_0(A), D, k2_tmap_1(B, A, D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_tmap_1)).
% 3.25/1.48  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.25/1.48  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.25/1.48  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.25/1.48  tff(f_61, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 3.25/1.48  tff(f_53, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.25/1.48  tff(f_83, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.25/1.48  tff(f_114, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (r1_funct_2(A, B, C, D, E, F) <=> (E = F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 3.25/1.48  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 3.25/1.48  tff(f_92, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 3.25/1.48  tff(f_67, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 3.25/1.48  tff(f_141, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 3.25/1.48  tff(f_29, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 3.25/1.48  tff(c_56, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_174])).
% 3.25/1.48  tff(c_20, plain, (![A_18]: (l1_struct_0(A_18) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.25/1.48  tff(c_60, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_174])).
% 3.25/1.48  tff(c_44, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_174])).
% 3.25/1.48  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_174])).
% 3.25/1.48  tff(c_72, plain, (![C_62, A_63, B_64]: (v1_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.25/1.48  tff(c_76, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_72])).
% 3.25/1.48  tff(c_77, plain, (![C_65, A_66, B_67]: (v4_relat_1(C_65, A_66) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.25/1.48  tff(c_81, plain, (v4_relat_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_77])).
% 3.25/1.48  tff(c_93, plain, (![B_73, A_74]: (k1_relat_1(B_73)=A_74 | ~v1_partfun1(B_73, A_74) | ~v4_relat_1(B_73, A_74) | ~v1_relat_1(B_73))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.25/1.48  tff(c_96, plain, (u1_struct_0('#skF_2')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', u1_struct_0('#skF_2')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_81, c_93])).
% 3.25/1.48  tff(c_99, plain, (u1_struct_0('#skF_2')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_96])).
% 3.25/1.48  tff(c_100, plain, (~v1_partfun1('#skF_4', u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_99])).
% 3.25/1.48  tff(c_42, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_174])).
% 3.25/1.48  tff(c_156, plain, (![C_93, A_94, B_95]: (v1_partfun1(C_93, A_94) | ~v1_funct_2(C_93, A_94, B_95) | ~v1_funct_1(C_93) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))) | v1_xboole_0(B_95))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.25/1.48  tff(c_159, plain, (v1_partfun1('#skF_4', u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_40, c_156])).
% 3.25/1.48  tff(c_162, plain, (v1_partfun1('#skF_4', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_159])).
% 3.25/1.48  tff(c_163, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_100, c_162])).
% 3.25/1.48  tff(c_24, plain, (![A_20]: (~v1_xboole_0(u1_struct_0(A_20)) | ~l1_struct_0(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.25/1.48  tff(c_166, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_163, c_24])).
% 3.25/1.48  tff(c_169, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_60, c_166])).
% 3.25/1.48  tff(c_172, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_169])).
% 3.25/1.48  tff(c_176, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_172])).
% 3.25/1.48  tff(c_177, plain, (u1_struct_0('#skF_2')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_99])).
% 3.25/1.48  tff(c_183, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_177, c_42])).
% 3.25/1.48  tff(c_182, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_177, c_40])).
% 3.25/1.48  tff(c_339, plain, (![B_119, F_116, A_120, D_118, C_117]: (r1_funct_2(A_120, B_119, C_117, D_118, F_116, F_116) | ~m1_subset_1(F_116, k1_zfmisc_1(k2_zfmisc_1(C_117, D_118))) | ~v1_funct_2(F_116, C_117, D_118) | ~m1_subset_1(F_116, k1_zfmisc_1(k2_zfmisc_1(A_120, B_119))) | ~v1_funct_2(F_116, A_120, B_119) | ~v1_funct_1(F_116) | v1_xboole_0(D_118) | v1_xboole_0(B_119))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.25/1.48  tff(c_341, plain, (![A_120, B_119]: (r1_funct_2(A_120, B_119, k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_120, B_119))) | ~v1_funct_2('#skF_4', A_120, B_119) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_119))), inference(resolution, [status(thm)], [c_182, c_339])).
% 3.25/1.48  tff(c_344, plain, (![A_120, B_119]: (r1_funct_2(A_120, B_119, k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_120, B_119))) | ~v1_funct_2('#skF_4', A_120, B_119) | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_119))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_183, c_341])).
% 3.25/1.48  tff(c_398, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_344])).
% 3.25/1.48  tff(c_401, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_398, c_24])).
% 3.25/1.48  tff(c_404, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_60, c_401])).
% 3.25/1.48  tff(c_408, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_404])).
% 3.25/1.48  tff(c_412, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_408])).
% 3.25/1.48  tff(c_414, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_344])).
% 3.25/1.48  tff(c_413, plain, (![A_120, B_119]: (r1_funct_2(A_120, B_119, k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_120, B_119))) | ~v1_funct_2('#skF_4', A_120, B_119) | v1_xboole_0(B_119))), inference(splitRight, [status(thm)], [c_344])).
% 3.25/1.48  tff(c_46, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_174])).
% 3.25/1.48  tff(c_50, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_174])).
% 3.25/1.48  tff(c_22, plain, (![A_19]: (m1_subset_1(u1_pre_topc(A_19), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_19)))) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.25/1.48  tff(c_187, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(k1_relat_1('#skF_4')))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_177, c_22])).
% 3.25/1.48  tff(c_194, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(k1_relat_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_187])).
% 3.25/1.48  tff(c_38, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_174])).
% 3.25/1.48  tff(c_180, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_177, c_38])).
% 3.25/1.48  tff(c_26, plain, (![D_26, B_22, C_25, A_21]: (D_26=B_22 | g1_pre_topc(C_25, D_26)!=g1_pre_topc(A_21, B_22) | ~m1_subset_1(B_22, k1_zfmisc_1(k1_zfmisc_1(A_21))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.25/1.48  tff(c_280, plain, (![B_112, A_113]: (u1_pre_topc('#skF_3')=B_112 | g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2'))!=g1_pre_topc(A_113, B_112) | ~m1_subset_1(B_112, k1_zfmisc_1(k1_zfmisc_1(A_113))))), inference(superposition, [status(thm), theory('equality')], [c_180, c_26])).
% 3.25/1.48  tff(c_287, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_194, c_280])).
% 3.25/1.48  tff(c_291, plain, (m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(k1_relat_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_287, c_194])).
% 3.25/1.48  tff(c_253, plain, (![C_100, A_101, D_102, B_103]: (C_100=A_101 | g1_pre_topc(C_100, D_102)!=g1_pre_topc(A_101, B_103) | ~m1_subset_1(B_103, k1_zfmisc_1(k1_zfmisc_1(A_101))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.25/1.48  tff(c_255, plain, (![A_101, B_103]: (u1_struct_0('#skF_3')=A_101 | g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2'))!=g1_pre_topc(A_101, B_103) | ~m1_subset_1(B_103, k1_zfmisc_1(k1_zfmisc_1(A_101))))), inference(superposition, [status(thm), theory('equality')], [c_180, c_253])).
% 3.25/1.48  tff(c_315, plain, (![A_114, B_115]: (u1_struct_0('#skF_3')=A_114 | g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_3'))!=g1_pre_topc(A_114, B_115) | ~m1_subset_1(B_115, k1_zfmisc_1(k1_zfmisc_1(A_114))))), inference(demodulation, [status(thm), theory('equality')], [c_287, c_255])).
% 3.25/1.48  tff(c_322, plain, (u1_struct_0('#skF_3')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_291, c_315])).
% 3.25/1.48  tff(c_58, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_174])).
% 3.25/1.48  tff(c_258, plain, (![A_104, B_105, C_106, D_107]: (k2_partfun1(A_104, B_105, C_106, D_107)=k7_relat_1(C_106, D_107) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))) | ~v1_funct_1(C_106))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.25/1.48  tff(c_260, plain, (![D_107]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', D_107)=k7_relat_1('#skF_4', D_107) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_182, c_258])).
% 3.25/1.48  tff(c_263, plain, (![D_107]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', D_107)=k7_relat_1('#skF_4', D_107))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_260])).
% 3.25/1.48  tff(c_54, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_174])).
% 3.25/1.48  tff(c_52, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_174])).
% 3.25/1.48  tff(c_424, plain, (![A_141, B_142, C_143, D_144]: (k2_partfun1(u1_struct_0(A_141), u1_struct_0(B_142), C_143, u1_struct_0(D_144))=k2_tmap_1(A_141, B_142, C_143, D_144) | ~m1_pre_topc(D_144, A_141) | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_141), u1_struct_0(B_142)))) | ~v1_funct_2(C_143, u1_struct_0(A_141), u1_struct_0(B_142)) | ~v1_funct_1(C_143) | ~l1_pre_topc(B_142) | ~v2_pre_topc(B_142) | v2_struct_0(B_142) | ~l1_pre_topc(A_141) | ~v2_pre_topc(A_141) | v2_struct_0(A_141))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.25/1.48  tff(c_430, plain, (![B_142, C_143, D_144]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0(B_142), C_143, u1_struct_0(D_144))=k2_tmap_1('#skF_2', B_142, C_143, D_144) | ~m1_pre_topc(D_144, '#skF_2') | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_142)))) | ~v1_funct_2(C_143, u1_struct_0('#skF_2'), u1_struct_0(B_142)) | ~v1_funct_1(C_143) | ~l1_pre_topc(B_142) | ~v2_pre_topc(B_142) | v2_struct_0(B_142) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_177, c_424])).
% 3.25/1.48  tff(c_438, plain, (![B_142, C_143, D_144]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0(B_142), C_143, u1_struct_0(D_144))=k2_tmap_1('#skF_2', B_142, C_143, D_144) | ~m1_pre_topc(D_144, '#skF_2') | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_142)))) | ~v1_funct_2(C_143, k1_relat_1('#skF_4'), u1_struct_0(B_142)) | ~v1_funct_1(C_143) | ~l1_pre_topc(B_142) | ~v2_pre_topc(B_142) | v2_struct_0(B_142) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_177, c_177, c_430])).
% 3.25/1.48  tff(c_443, plain, (![B_145, C_146, D_147]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0(B_145), C_146, u1_struct_0(D_147))=k2_tmap_1('#skF_2', B_145, C_146, D_147) | ~m1_pre_topc(D_147, '#skF_2') | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_145)))) | ~v1_funct_2(C_146, k1_relat_1('#skF_4'), u1_struct_0(B_145)) | ~v1_funct_1(C_146) | ~l1_pre_topc(B_145) | ~v2_pre_topc(B_145) | v2_struct_0(B_145))), inference(negUnitSimplification, [status(thm)], [c_54, c_438])).
% 3.25/1.48  tff(c_447, plain, (![D_147]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_147))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_147) | ~m1_pre_topc(D_147, '#skF_2') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_182, c_443])).
% 3.25/1.48  tff(c_454, plain, (![D_147]: (k7_relat_1('#skF_4', u1_struct_0(D_147))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_147) | ~m1_pre_topc(D_147, '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_44, c_183, c_263, c_447])).
% 3.25/1.48  tff(c_459, plain, (![D_148]: (k7_relat_1('#skF_4', u1_struct_0(D_148))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_148) | ~m1_pre_topc(D_148, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_60, c_454])).
% 3.25/1.48  tff(c_468, plain, (k7_relat_1('#skF_4', k1_relat_1('#skF_4'))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_322, c_459])).
% 3.25/1.48  tff(c_475, plain, (k7_relat_1('#skF_4', k1_relat_1('#skF_4'))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_468])).
% 3.25/1.48  tff(c_2, plain, (![A_1]: (k7_relat_1(A_1, k1_relat_1(A_1))=A_1 | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.25/1.48  tff(c_479, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_475, c_2])).
% 3.25/1.48  tff(c_486, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_479])).
% 3.25/1.48  tff(c_36, plain, (~r1_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_174])).
% 3.25/1.48  tff(c_179, plain, (~r1_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_177, c_36])).
% 3.25/1.48  tff(c_326, plain, (~r1_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_322, c_179])).
% 3.25/1.48  tff(c_491, plain, (~r1_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_486, c_326])).
% 3.25/1.48  tff(c_525, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_413, c_491])).
% 3.25/1.48  tff(c_528, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_183, c_182, c_525])).
% 3.25/1.48  tff(c_530, plain, $false, inference(negUnitSimplification, [status(thm)], [c_414, c_528])).
% 3.25/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.48  
% 3.25/1.48  Inference rules
% 3.25/1.48  ----------------------
% 3.25/1.48  #Ref     : 7
% 3.25/1.48  #Sup     : 92
% 3.25/1.48  #Fact    : 0
% 3.25/1.48  #Define  : 0
% 3.25/1.48  #Split   : 4
% 3.25/1.48  #Chain   : 0
% 3.25/1.48  #Close   : 0
% 3.25/1.48  
% 3.25/1.48  Ordering : KBO
% 3.25/1.48  
% 3.25/1.48  Simplification rules
% 3.25/1.48  ----------------------
% 3.25/1.48  #Subsume      : 9
% 3.25/1.48  #Demod        : 109
% 3.25/1.48  #Tautology    : 53
% 3.25/1.48  #SimpNegUnit  : 16
% 3.25/1.48  #BackRed      : 12
% 3.25/1.48  
% 3.25/1.48  #Partial instantiations: 0
% 3.25/1.48  #Strategies tried      : 1
% 3.25/1.48  
% 3.25/1.48  Timing (in seconds)
% 3.25/1.48  ----------------------
% 3.33/1.49  Preprocessing        : 0.37
% 3.33/1.49  Parsing              : 0.20
% 3.33/1.49  CNF conversion       : 0.03
% 3.33/1.49  Main loop            : 0.35
% 3.33/1.49  Inferencing          : 0.12
% 3.33/1.49  Reduction            : 0.11
% 3.33/1.49  Demodulation         : 0.08
% 3.33/1.49  BG Simplification    : 0.02
% 3.33/1.49  Subsumption          : 0.06
% 3.33/1.49  Abstraction          : 0.02
% 3.33/1.49  MUC search           : 0.00
% 3.33/1.49  Cooper               : 0.00
% 3.33/1.49  Total                : 0.77
% 3.33/1.49  Index Insertion      : 0.00
% 3.33/1.49  Index Deletion       : 0.00
% 3.33/1.49  Index Matching       : 0.00
% 3.33/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
