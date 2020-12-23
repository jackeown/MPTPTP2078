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
% DateTime   : Thu Dec  3 10:26:53 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 672 expanded)
%              Number of leaves         :   43 ( 239 expanded)
%              Depth                    :   19
%              Number of atoms          :  250 (2493 expanded)
%              Number of equality atoms :   41 ( 322 expanded)
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

tff(f_179,negated_conjecture,(
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

tff(f_90,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_119,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( ~ v1_xboole_0(B)
        & ~ v1_xboole_0(D)
        & v1_funct_1(E)
        & v1_funct_2(E,A,B)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & v1_funct_2(F,C,D)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => r1_funct_2(A,B,C,D,E,E) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r1_funct_2)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_99,axiom,(
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

tff(f_146,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_20,plain,(
    ! [A_18] :
      ( l1_struct_0(A_18)
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_44,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_4,plain,(
    ! [C_4,A_2,B_3] :
      ( v1_relat_1(C_4)
      | ~ m1_subset_1(C_4,k1_zfmisc_1(k2_zfmisc_1(A_2,B_3))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_83,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_4])).

tff(c_94,plain,(
    ! [C_74,A_75,B_76] :
      ( v4_relat_1(C_74,A_75)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_98,plain,(
    v4_relat_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_94])).

tff(c_100,plain,(
    ! [B_78,A_79] :
      ( k1_relat_1(B_78) = A_79
      | ~ v1_partfun1(B_78,A_79)
      | ~ v4_relat_1(B_78,A_79)
      | ~ v1_relat_1(B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_103,plain,
    ( u1_struct_0('#skF_2') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',u1_struct_0('#skF_2'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_98,c_100])).

tff(c_106,plain,
    ( u1_struct_0('#skF_2') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_103])).

tff(c_107,plain,(
    ~ v1_partfun1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_42,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_151,plain,(
    ! [C_97,A_98,B_99] :
      ( v1_partfun1(C_97,A_98)
      | ~ v1_funct_2(C_97,A_98,B_99)
      | ~ v1_funct_1(C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99)))
      | v1_xboole_0(B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_154,plain,
    ( v1_partfun1('#skF_4',u1_struct_0('#skF_2'))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_40,c_151])).

tff(c_157,plain,
    ( v1_partfun1('#skF_4',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_154])).

tff(c_158,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_157])).

tff(c_26,plain,(
    ! [A_23] :
      ( ~ v1_xboole_0(u1_struct_0(A_23))
      | ~ l1_struct_0(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_161,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_158,c_26])).

tff(c_164,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_161])).

tff(c_167,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_164])).

tff(c_171,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_167])).

tff(c_172,plain,(
    u1_struct_0('#skF_2') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_177,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_42])).

tff(c_176,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_40])).

tff(c_355,plain,(
    ! [C_121,A_124,B_122,D_126,F_123,E_125] :
      ( r1_funct_2(A_124,B_122,C_121,D_126,E_125,E_125)
      | ~ m1_subset_1(F_123,k1_zfmisc_1(k2_zfmisc_1(C_121,D_126)))
      | ~ v1_funct_2(F_123,C_121,D_126)
      | ~ v1_funct_1(F_123)
      | ~ m1_subset_1(E_125,k1_zfmisc_1(k2_zfmisc_1(A_124,B_122)))
      | ~ v1_funct_2(E_125,A_124,B_122)
      | ~ v1_funct_1(E_125)
      | v1_xboole_0(D_126)
      | v1_xboole_0(B_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_357,plain,(
    ! [A_124,B_122,E_125] :
      ( r1_funct_2(A_124,B_122,k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),E_125,E_125)
      | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_125,k1_zfmisc_1(k2_zfmisc_1(A_124,B_122)))
      | ~ v1_funct_2(E_125,A_124,B_122)
      | ~ v1_funct_1(E_125)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_122) ) ),
    inference(resolution,[status(thm)],[c_176,c_355])).

tff(c_360,plain,(
    ! [A_124,B_122,E_125] :
      ( r1_funct_2(A_124,B_122,k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),E_125,E_125)
      | ~ m1_subset_1(E_125,k1_zfmisc_1(k2_zfmisc_1(A_124,B_122)))
      | ~ v1_funct_2(E_125,A_124,B_122)
      | ~ v1_funct_1(E_125)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_122) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_177,c_357])).

tff(c_398,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_360])).

tff(c_401,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_398,c_26])).

tff(c_404,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_401])).

tff(c_407,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_404])).

tff(c_411,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_407])).

tff(c_413,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_360])).

tff(c_412,plain,(
    ! [A_124,B_122,E_125] :
      ( r1_funct_2(A_124,B_122,k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),E_125,E_125)
      | ~ m1_subset_1(E_125,k1_zfmisc_1(k2_zfmisc_1(A_124,B_122)))
      | ~ v1_funct_2(E_125,A_124,B_122)
      | ~ v1_funct_1(E_125)
      | v1_xboole_0(B_122) ) ),
    inference(splitRight,[status(thm)],[c_360])).

tff(c_46,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_50,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_24,plain,(
    ! [A_22] :
      ( m1_subset_1(u1_pre_topc(A_22),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_22))))
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_181,plain,
    ( m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(k1_relat_1('#skF_4'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_24])).

tff(c_188,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(k1_relat_1('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_181])).

tff(c_38,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_175,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_38])).

tff(c_28,plain,(
    ! [D_29,B_25,C_28,A_24] :
      ( D_29 = B_25
      | g1_pre_topc(C_28,D_29) != g1_pre_topc(A_24,B_25)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(k1_zfmisc_1(A_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_276,plain,(
    ! [B_116,A_117] :
      ( u1_pre_topc('#skF_3') = B_116
      | g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2')) != g1_pre_topc(A_117,B_116)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(k1_zfmisc_1(A_117))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_28])).

tff(c_283,plain,(
    u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_188,c_276])).

tff(c_287,plain,(
    m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(k1_relat_1('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_188])).

tff(c_249,plain,(
    ! [C_104,A_105,D_106,B_107] :
      ( C_104 = A_105
      | g1_pre_topc(C_104,D_106) != g1_pre_topc(A_105,B_107)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(k1_zfmisc_1(A_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_251,plain,(
    ! [A_105,B_107] :
      ( u1_struct_0('#skF_3') = A_105
      | g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2')) != g1_pre_topc(A_105,B_107)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(k1_zfmisc_1(A_105))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_249])).

tff(c_311,plain,(
    ! [A_118,B_119] :
      ( u1_struct_0('#skF_3') = A_118
      | g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_3')) != g1_pre_topc(A_118,B_119)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(k1_zfmisc_1(A_118))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_251])).

tff(c_318,plain,(
    u1_struct_0('#skF_3') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_287,c_311])).

tff(c_58,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_254,plain,(
    ! [A_108,B_109,C_110,D_111] :
      ( k2_partfun1(A_108,B_109,C_110,D_111) = k7_relat_1(C_110,D_111)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109)))
      | ~ v1_funct_1(C_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_256,plain,(
    ! [D_111] :
      ( k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4',D_111) = k7_relat_1('#skF_4',D_111)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_176,c_254])).

tff(c_259,plain,(
    ! [D_111] : k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4',D_111) = k7_relat_1('#skF_4',D_111) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_256])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_52,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_414,plain,(
    ! [A_132,B_133,C_134,D_135] :
      ( k2_partfun1(u1_struct_0(A_132),u1_struct_0(B_133),C_134,u1_struct_0(D_135)) = k2_tmap_1(A_132,B_133,C_134,D_135)
      | ~ m1_pre_topc(D_135,A_132)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_132),u1_struct_0(B_133))))
      | ~ v1_funct_2(C_134,u1_struct_0(A_132),u1_struct_0(B_133))
      | ~ v1_funct_1(C_134)
      | ~ l1_pre_topc(B_133)
      | ~ v2_pre_topc(B_133)
      | v2_struct_0(B_133)
      | ~ l1_pre_topc(A_132)
      | ~ v2_pre_topc(A_132)
      | v2_struct_0(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_420,plain,(
    ! [B_133,C_134,D_135] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0(B_133),C_134,u1_struct_0(D_135)) = k2_tmap_1('#skF_2',B_133,C_134,D_135)
      | ~ m1_pre_topc(D_135,'#skF_2')
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_133))))
      | ~ v1_funct_2(C_134,u1_struct_0('#skF_2'),u1_struct_0(B_133))
      | ~ v1_funct_1(C_134)
      | ~ l1_pre_topc(B_133)
      | ~ v2_pre_topc(B_133)
      | v2_struct_0(B_133)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_414])).

tff(c_430,plain,(
    ! [B_133,C_134,D_135] :
      ( k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0(B_133),C_134,u1_struct_0(D_135)) = k2_tmap_1('#skF_2',B_133,C_134,D_135)
      | ~ m1_pre_topc(D_135,'#skF_2')
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_133))))
      | ~ v1_funct_2(C_134,k1_relat_1('#skF_4'),u1_struct_0(B_133))
      | ~ v1_funct_1(C_134)
      | ~ l1_pre_topc(B_133)
      | ~ v2_pre_topc(B_133)
      | v2_struct_0(B_133)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_172,c_172,c_420])).

tff(c_436,plain,(
    ! [B_139,C_140,D_141] :
      ( k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0(B_139),C_140,u1_struct_0(D_141)) = k2_tmap_1('#skF_2',B_139,C_140,D_141)
      | ~ m1_pre_topc(D_141,'#skF_2')
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_139))))
      | ~ v1_funct_2(C_140,k1_relat_1('#skF_4'),u1_struct_0(B_139))
      | ~ v1_funct_1(C_140)
      | ~ l1_pre_topc(B_139)
      | ~ v2_pre_topc(B_139)
      | v2_struct_0(B_139) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_430])).

tff(c_440,plain,(
    ! [D_141] :
      ( k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_141)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_141)
      | ~ m1_pre_topc(D_141,'#skF_2')
      | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_176,c_436])).

tff(c_448,plain,(
    ! [D_141] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_141)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_141)
      | ~ m1_pre_topc(D_141,'#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_44,c_177,c_259,c_440])).

tff(c_453,plain,(
    ! [D_142] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_142)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_142)
      | ~ m1_pre_topc(D_142,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_448])).

tff(c_462,plain,
    ( k7_relat_1('#skF_4',k1_relat_1('#skF_4')) = k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_318,c_453])).

tff(c_469,plain,(
    k7_relat_1('#skF_4',k1_relat_1('#skF_4')) = k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_462])).

tff(c_2,plain,(
    ! [A_1] :
      ( k7_relat_1(A_1,k1_relat_1(A_1)) = A_1
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_473,plain,
    ( k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_469,c_2])).

tff(c_480,plain,(
    k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_473])).

tff(c_36,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_191,plain,(
    ~ r1_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_36])).

tff(c_322,plain,(
    ~ r1_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_191])).

tff(c_485,plain,(
    ~ r1_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_480,c_322])).

tff(c_509,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'))))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_1'))
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_412,c_485])).

tff(c_512,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_177,c_176,c_509])).

tff(c_514,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_413,c_512])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:36:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.81/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.39  
% 2.81/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.40  %$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.81/1.40  
% 2.81/1.40  %Foreground sorts:
% 2.81/1.40  
% 2.81/1.40  
% 2.81/1.40  %Background operators:
% 2.81/1.40  
% 2.81/1.40  
% 2.81/1.40  %Foreground operators:
% 2.81/1.40  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.81/1.40  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.81/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.81/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.81/1.40  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 2.81/1.40  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.81/1.40  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.81/1.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.81/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.81/1.40  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.81/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.81/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.81/1.40  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.81/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.81/1.40  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.81/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.81/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.81/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.81/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.81/1.40  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 2.81/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.81/1.40  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.81/1.40  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.81/1.40  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.81/1.40  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.81/1.40  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 2.81/1.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.81/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.81/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.81/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.81/1.40  
% 2.81/1.42  tff(f_179, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => r1_funct_2(u1_struct_0(B), u1_struct_0(A), u1_struct_0(C), u1_struct_0(A), D, k2_tmap_1(B, A, D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_tmap_1)).
% 2.81/1.42  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.81/1.42  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.81/1.42  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.81/1.42  tff(f_61, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 2.81/1.42  tff(f_53, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.81/1.42  tff(f_90, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.81/1.42  tff(f_119, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => r1_funct_2(A, B, C, D, E, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r1_funct_2)).
% 2.81/1.42  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 2.81/1.42  tff(f_99, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 2.81/1.42  tff(f_67, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.81/1.42  tff(f_146, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 2.81/1.42  tff(f_29, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 2.81/1.42  tff(c_56, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_179])).
% 2.81/1.42  tff(c_20, plain, (![A_18]: (l1_struct_0(A_18) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.81/1.42  tff(c_60, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_179])).
% 2.81/1.42  tff(c_44, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_179])).
% 2.81/1.42  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_179])).
% 2.81/1.42  tff(c_4, plain, (![C_4, A_2, B_3]: (v1_relat_1(C_4) | ~m1_subset_1(C_4, k1_zfmisc_1(k2_zfmisc_1(A_2, B_3))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.81/1.42  tff(c_83, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_4])).
% 2.81/1.42  tff(c_94, plain, (![C_74, A_75, B_76]: (v4_relat_1(C_74, A_75) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.81/1.42  tff(c_98, plain, (v4_relat_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_94])).
% 2.81/1.42  tff(c_100, plain, (![B_78, A_79]: (k1_relat_1(B_78)=A_79 | ~v1_partfun1(B_78, A_79) | ~v4_relat_1(B_78, A_79) | ~v1_relat_1(B_78))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.81/1.42  tff(c_103, plain, (u1_struct_0('#skF_2')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', u1_struct_0('#skF_2')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_98, c_100])).
% 2.81/1.42  tff(c_106, plain, (u1_struct_0('#skF_2')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_103])).
% 2.81/1.42  tff(c_107, plain, (~v1_partfun1('#skF_4', u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_106])).
% 2.81/1.42  tff(c_42, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_179])).
% 2.81/1.42  tff(c_151, plain, (![C_97, A_98, B_99]: (v1_partfun1(C_97, A_98) | ~v1_funct_2(C_97, A_98, B_99) | ~v1_funct_1(C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))) | v1_xboole_0(B_99))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.81/1.42  tff(c_154, plain, (v1_partfun1('#skF_4', u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_40, c_151])).
% 2.81/1.42  tff(c_157, plain, (v1_partfun1('#skF_4', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_154])).
% 2.81/1.42  tff(c_158, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_107, c_157])).
% 2.81/1.42  tff(c_26, plain, (![A_23]: (~v1_xboole_0(u1_struct_0(A_23)) | ~l1_struct_0(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.81/1.42  tff(c_161, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_158, c_26])).
% 2.81/1.42  tff(c_164, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_60, c_161])).
% 2.81/1.42  tff(c_167, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_164])).
% 2.81/1.42  tff(c_171, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_167])).
% 2.81/1.42  tff(c_172, plain, (u1_struct_0('#skF_2')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_106])).
% 2.81/1.42  tff(c_177, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_42])).
% 2.81/1.42  tff(c_176, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_40])).
% 2.81/1.42  tff(c_355, plain, (![C_121, A_124, B_122, D_126, F_123, E_125]: (r1_funct_2(A_124, B_122, C_121, D_126, E_125, E_125) | ~m1_subset_1(F_123, k1_zfmisc_1(k2_zfmisc_1(C_121, D_126))) | ~v1_funct_2(F_123, C_121, D_126) | ~v1_funct_1(F_123) | ~m1_subset_1(E_125, k1_zfmisc_1(k2_zfmisc_1(A_124, B_122))) | ~v1_funct_2(E_125, A_124, B_122) | ~v1_funct_1(E_125) | v1_xboole_0(D_126) | v1_xboole_0(B_122))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.81/1.42  tff(c_357, plain, (![A_124, B_122, E_125]: (r1_funct_2(A_124, B_122, k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), E_125, E_125) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_125, k1_zfmisc_1(k2_zfmisc_1(A_124, B_122))) | ~v1_funct_2(E_125, A_124, B_122) | ~v1_funct_1(E_125) | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_122))), inference(resolution, [status(thm)], [c_176, c_355])).
% 2.81/1.42  tff(c_360, plain, (![A_124, B_122, E_125]: (r1_funct_2(A_124, B_122, k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), E_125, E_125) | ~m1_subset_1(E_125, k1_zfmisc_1(k2_zfmisc_1(A_124, B_122))) | ~v1_funct_2(E_125, A_124, B_122) | ~v1_funct_1(E_125) | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_122))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_177, c_357])).
% 2.81/1.42  tff(c_398, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_360])).
% 2.81/1.42  tff(c_401, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_398, c_26])).
% 2.81/1.42  tff(c_404, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_60, c_401])).
% 2.81/1.42  tff(c_407, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_404])).
% 2.81/1.42  tff(c_411, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_407])).
% 2.81/1.42  tff(c_413, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_360])).
% 2.81/1.42  tff(c_412, plain, (![A_124, B_122, E_125]: (r1_funct_2(A_124, B_122, k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), E_125, E_125) | ~m1_subset_1(E_125, k1_zfmisc_1(k2_zfmisc_1(A_124, B_122))) | ~v1_funct_2(E_125, A_124, B_122) | ~v1_funct_1(E_125) | v1_xboole_0(B_122))), inference(splitRight, [status(thm)], [c_360])).
% 2.81/1.42  tff(c_46, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_179])).
% 2.81/1.42  tff(c_50, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_179])).
% 2.81/1.42  tff(c_24, plain, (![A_22]: (m1_subset_1(u1_pre_topc(A_22), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_22)))) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.81/1.42  tff(c_181, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(k1_relat_1('#skF_4')))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_172, c_24])).
% 2.81/1.42  tff(c_188, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(k1_relat_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_181])).
% 2.81/1.42  tff(c_38, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_179])).
% 2.81/1.42  tff(c_175, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_38])).
% 2.81/1.42  tff(c_28, plain, (![D_29, B_25, C_28, A_24]: (D_29=B_25 | g1_pre_topc(C_28, D_29)!=g1_pre_topc(A_24, B_25) | ~m1_subset_1(B_25, k1_zfmisc_1(k1_zfmisc_1(A_24))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.81/1.42  tff(c_276, plain, (![B_116, A_117]: (u1_pre_topc('#skF_3')=B_116 | g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2'))!=g1_pre_topc(A_117, B_116) | ~m1_subset_1(B_116, k1_zfmisc_1(k1_zfmisc_1(A_117))))), inference(superposition, [status(thm), theory('equality')], [c_175, c_28])).
% 2.81/1.42  tff(c_283, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_188, c_276])).
% 2.81/1.42  tff(c_287, plain, (m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(k1_relat_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_283, c_188])).
% 2.81/1.42  tff(c_249, plain, (![C_104, A_105, D_106, B_107]: (C_104=A_105 | g1_pre_topc(C_104, D_106)!=g1_pre_topc(A_105, B_107) | ~m1_subset_1(B_107, k1_zfmisc_1(k1_zfmisc_1(A_105))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.81/1.42  tff(c_251, plain, (![A_105, B_107]: (u1_struct_0('#skF_3')=A_105 | g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2'))!=g1_pre_topc(A_105, B_107) | ~m1_subset_1(B_107, k1_zfmisc_1(k1_zfmisc_1(A_105))))), inference(superposition, [status(thm), theory('equality')], [c_175, c_249])).
% 2.81/1.42  tff(c_311, plain, (![A_118, B_119]: (u1_struct_0('#skF_3')=A_118 | g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_3'))!=g1_pre_topc(A_118, B_119) | ~m1_subset_1(B_119, k1_zfmisc_1(k1_zfmisc_1(A_118))))), inference(demodulation, [status(thm), theory('equality')], [c_283, c_251])).
% 2.81/1.42  tff(c_318, plain, (u1_struct_0('#skF_3')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_287, c_311])).
% 2.81/1.42  tff(c_58, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_179])).
% 2.81/1.42  tff(c_254, plain, (![A_108, B_109, C_110, D_111]: (k2_partfun1(A_108, B_109, C_110, D_111)=k7_relat_1(C_110, D_111) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))) | ~v1_funct_1(C_110))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.81/1.42  tff(c_256, plain, (![D_111]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', D_111)=k7_relat_1('#skF_4', D_111) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_176, c_254])).
% 2.81/1.42  tff(c_259, plain, (![D_111]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', D_111)=k7_relat_1('#skF_4', D_111))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_256])).
% 2.81/1.42  tff(c_54, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_179])).
% 2.81/1.42  tff(c_52, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_179])).
% 2.81/1.42  tff(c_414, plain, (![A_132, B_133, C_134, D_135]: (k2_partfun1(u1_struct_0(A_132), u1_struct_0(B_133), C_134, u1_struct_0(D_135))=k2_tmap_1(A_132, B_133, C_134, D_135) | ~m1_pre_topc(D_135, A_132) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_132), u1_struct_0(B_133)))) | ~v1_funct_2(C_134, u1_struct_0(A_132), u1_struct_0(B_133)) | ~v1_funct_1(C_134) | ~l1_pre_topc(B_133) | ~v2_pre_topc(B_133) | v2_struct_0(B_133) | ~l1_pre_topc(A_132) | ~v2_pre_topc(A_132) | v2_struct_0(A_132))), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.81/1.42  tff(c_420, plain, (![B_133, C_134, D_135]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0(B_133), C_134, u1_struct_0(D_135))=k2_tmap_1('#skF_2', B_133, C_134, D_135) | ~m1_pre_topc(D_135, '#skF_2') | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_133)))) | ~v1_funct_2(C_134, u1_struct_0('#skF_2'), u1_struct_0(B_133)) | ~v1_funct_1(C_134) | ~l1_pre_topc(B_133) | ~v2_pre_topc(B_133) | v2_struct_0(B_133) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_172, c_414])).
% 2.81/1.42  tff(c_430, plain, (![B_133, C_134, D_135]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0(B_133), C_134, u1_struct_0(D_135))=k2_tmap_1('#skF_2', B_133, C_134, D_135) | ~m1_pre_topc(D_135, '#skF_2') | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_133)))) | ~v1_funct_2(C_134, k1_relat_1('#skF_4'), u1_struct_0(B_133)) | ~v1_funct_1(C_134) | ~l1_pre_topc(B_133) | ~v2_pre_topc(B_133) | v2_struct_0(B_133) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_172, c_172, c_420])).
% 2.81/1.42  tff(c_436, plain, (![B_139, C_140, D_141]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0(B_139), C_140, u1_struct_0(D_141))=k2_tmap_1('#skF_2', B_139, C_140, D_141) | ~m1_pre_topc(D_141, '#skF_2') | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_139)))) | ~v1_funct_2(C_140, k1_relat_1('#skF_4'), u1_struct_0(B_139)) | ~v1_funct_1(C_140) | ~l1_pre_topc(B_139) | ~v2_pre_topc(B_139) | v2_struct_0(B_139))), inference(negUnitSimplification, [status(thm)], [c_54, c_430])).
% 2.81/1.42  tff(c_440, plain, (![D_141]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_141))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_141) | ~m1_pre_topc(D_141, '#skF_2') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_176, c_436])).
% 2.81/1.42  tff(c_448, plain, (![D_141]: (k7_relat_1('#skF_4', u1_struct_0(D_141))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_141) | ~m1_pre_topc(D_141, '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_44, c_177, c_259, c_440])).
% 2.81/1.42  tff(c_453, plain, (![D_142]: (k7_relat_1('#skF_4', u1_struct_0(D_142))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_142) | ~m1_pre_topc(D_142, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_60, c_448])).
% 2.81/1.42  tff(c_462, plain, (k7_relat_1('#skF_4', k1_relat_1('#skF_4'))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_318, c_453])).
% 2.81/1.42  tff(c_469, plain, (k7_relat_1('#skF_4', k1_relat_1('#skF_4'))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_462])).
% 2.81/1.42  tff(c_2, plain, (![A_1]: (k7_relat_1(A_1, k1_relat_1(A_1))=A_1 | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.81/1.42  tff(c_473, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_469, c_2])).
% 2.81/1.42  tff(c_480, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_83, c_473])).
% 2.81/1.42  tff(c_36, plain, (~r1_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_179])).
% 2.81/1.42  tff(c_191, plain, (~r1_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_36])).
% 2.81/1.42  tff(c_322, plain, (~r1_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_318, c_191])).
% 2.81/1.42  tff(c_485, plain, (~r1_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_480, c_322])).
% 2.81/1.42  tff(c_509, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_412, c_485])).
% 2.81/1.42  tff(c_512, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_177, c_176, c_509])).
% 2.81/1.42  tff(c_514, plain, $false, inference(negUnitSimplification, [status(thm)], [c_413, c_512])).
% 2.81/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.42  
% 2.81/1.42  Inference rules
% 2.81/1.42  ----------------------
% 2.81/1.42  #Ref     : 6
% 2.81/1.42  #Sup     : 89
% 2.81/1.42  #Fact    : 0
% 2.81/1.42  #Define  : 0
% 2.81/1.42  #Split   : 3
% 2.81/1.42  #Chain   : 0
% 2.81/1.42  #Close   : 0
% 2.81/1.42  
% 2.81/1.42  Ordering : KBO
% 2.81/1.42  
% 2.81/1.42  Simplification rules
% 2.81/1.42  ----------------------
% 2.81/1.42  #Subsume      : 9
% 2.81/1.42  #Demod        : 106
% 2.81/1.42  #Tautology    : 51
% 2.81/1.42  #SimpNegUnit  : 13
% 2.81/1.42  #BackRed      : 11
% 2.81/1.42  
% 2.81/1.42  #Partial instantiations: 0
% 2.81/1.42  #Strategies tried      : 1
% 2.81/1.42  
% 3.03/1.42  Timing (in seconds)
% 3.03/1.42  ----------------------
% 3.03/1.42  Preprocessing        : 0.35
% 3.03/1.42  Parsing              : 0.19
% 3.03/1.42  CNF conversion       : 0.02
% 3.03/1.42  Main loop            : 0.30
% 3.03/1.42  Inferencing          : 0.10
% 3.03/1.42  Reduction            : 0.10
% 3.03/1.42  Demodulation         : 0.07
% 3.03/1.42  BG Simplification    : 0.02
% 3.03/1.42  Subsumption          : 0.05
% 3.03/1.42  Abstraction          : 0.02
% 3.03/1.42  MUC search           : 0.00
% 3.03/1.42  Cooper               : 0.00
% 3.03/1.42  Total                : 0.69
% 3.03/1.42  Index Insertion      : 0.00
% 3.03/1.42  Index Deletion       : 0.00
% 3.03/1.42  Index Matching       : 0.00
% 3.03/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
