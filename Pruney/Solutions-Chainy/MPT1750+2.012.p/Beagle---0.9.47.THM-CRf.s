%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:52 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 500 expanded)
%              Number of leaves         :   45 ( 185 expanded)
%              Depth                    :   19
%              Number of atoms          :  247 (1881 expanded)
%              Number of equality atoms :   36 ( 216 expanded)
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

tff(f_180,negated_conjecture,(
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

tff(f_91,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_120,axiom,(
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

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_100,axiom,(
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

tff(f_147,axiom,(
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

tff(c_60,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_26,plain,(
    ! [A_21] :
      ( l1_struct_0(A_21)
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_48,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_69,plain,(
    ! [C_65,A_66,B_67] :
      ( v1_relat_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_73,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_69])).

tff(c_90,plain,(
    ! [C_73,A_74,B_75] :
      ( v4_relat_1(C_73,A_74)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_94,plain,(
    v4_relat_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_44,c_90])).

tff(c_112,plain,(
    ! [B_81,A_82] :
      ( k1_relat_1(B_81) = A_82
      | ~ v1_partfun1(B_81,A_82)
      | ~ v4_relat_1(B_81,A_82)
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_115,plain,
    ( u1_struct_0('#skF_2') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',u1_struct_0('#skF_2'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_94,c_112])).

tff(c_118,plain,
    ( u1_struct_0('#skF_2') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_115])).

tff(c_119,plain,(
    ~ v1_partfun1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_118])).

tff(c_46,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_158,plain,(
    ! [C_98,A_99,B_100] :
      ( v1_partfun1(C_98,A_99)
      | ~ v1_funct_2(C_98,A_99,B_100)
      | ~ v1_funct_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100)))
      | v1_xboole_0(B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_161,plain,
    ( v1_partfun1('#skF_4',u1_struct_0('#skF_2'))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_44,c_158])).

tff(c_164,plain,
    ( v1_partfun1('#skF_4',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_161])).

tff(c_165,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_164])).

tff(c_30,plain,(
    ! [A_23] :
      ( ~ v1_xboole_0(u1_struct_0(A_23))
      | ~ l1_struct_0(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_168,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_165,c_30])).

tff(c_171,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_168])).

tff(c_174,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_171])).

tff(c_178,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_174])).

tff(c_179,plain,(
    u1_struct_0('#skF_2') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_184,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_46])).

tff(c_183,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_44])).

tff(c_345,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_347,plain,(
    ! [A_124,B_122,E_125] :
      ( r1_funct_2(A_124,B_122,k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),E_125,E_125)
      | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_125,k1_zfmisc_1(k2_zfmisc_1(A_124,B_122)))
      | ~ v1_funct_2(E_125,A_124,B_122)
      | ~ v1_funct_1(E_125)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_122) ) ),
    inference(resolution,[status(thm)],[c_183,c_345])).

tff(c_350,plain,(
    ! [A_124,B_122,E_125] :
      ( r1_funct_2(A_124,B_122,k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),E_125,E_125)
      | ~ m1_subset_1(E_125,k1_zfmisc_1(k2_zfmisc_1(A_124,B_122)))
      | ~ v1_funct_2(E_125,A_124,B_122)
      | ~ v1_funct_1(E_125)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_122) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_184,c_347])).

tff(c_368,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_350])).

tff(c_390,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_368,c_30])).

tff(c_393,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_390])).

tff(c_396,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_393])).

tff(c_400,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_396])).

tff(c_402,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_350])).

tff(c_401,plain,(
    ! [A_124,B_122,E_125] :
      ( r1_funct_2(A_124,B_122,k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),E_125,E_125)
      | ~ m1_subset_1(E_125,k1_zfmisc_1(k2_zfmisc_1(A_124,B_122)))
      | ~ v1_funct_2(E_125,A_124,B_122)
      | ~ v1_funct_1(E_125)
      | v1_xboole_0(B_122) ) ),
    inference(splitRight,[status(thm)],[c_350])).

tff(c_50,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_54,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_28,plain,(
    ! [A_22] :
      ( m1_subset_1(u1_pre_topc(A_22),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_22))))
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_188,plain,
    ( m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(k1_relat_1('#skF_4'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_28])).

tff(c_195,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(k1_relat_1('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_188])).

tff(c_42,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_182,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_42])).

tff(c_34,plain,(
    ! [C_28,A_24,D_29,B_25] :
      ( C_28 = A_24
      | g1_pre_topc(C_28,D_29) != g1_pre_topc(A_24,B_25)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(k1_zfmisc_1(A_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_283,plain,(
    ! [A_117,B_118] :
      ( u1_struct_0('#skF_3') = A_117
      | g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2')) != g1_pre_topc(A_117,B_118)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(k1_zfmisc_1(A_117))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_34])).

tff(c_290,plain,(
    u1_struct_0('#skF_3') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_195,c_283])).

tff(c_62,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_261,plain,(
    ! [A_109,B_110,C_111,D_112] :
      ( k2_partfun1(A_109,B_110,C_111,D_112) = k7_relat_1(C_111,D_112)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110)))
      | ~ v1_funct_1(C_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_263,plain,(
    ! [D_112] :
      ( k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4',D_112) = k7_relat_1('#skF_4',D_112)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_183,c_261])).

tff(c_266,plain,(
    ! [D_112] : k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4',D_112) = k7_relat_1('#skF_4',D_112) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_263])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_56,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_404,plain,(
    ! [A_138,B_139,C_140,D_141] :
      ( k2_partfun1(u1_struct_0(A_138),u1_struct_0(B_139),C_140,u1_struct_0(D_141)) = k2_tmap_1(A_138,B_139,C_140,D_141)
      | ~ m1_pre_topc(D_141,A_138)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_138),u1_struct_0(B_139))))
      | ~ v1_funct_2(C_140,u1_struct_0(A_138),u1_struct_0(B_139))
      | ~ v1_funct_1(C_140)
      | ~ l1_pre_topc(B_139)
      | ~ v2_pre_topc(B_139)
      | v2_struct_0(B_139)
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_410,plain,(
    ! [B_139,C_140,D_141] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0(B_139),C_140,u1_struct_0(D_141)) = k2_tmap_1('#skF_2',B_139,C_140,D_141)
      | ~ m1_pre_topc(D_141,'#skF_2')
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_139))))
      | ~ v1_funct_2(C_140,u1_struct_0('#skF_2'),u1_struct_0(B_139))
      | ~ v1_funct_1(C_140)
      | ~ l1_pre_topc(B_139)
      | ~ v2_pre_topc(B_139)
      | v2_struct_0(B_139)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_404])).

tff(c_418,plain,(
    ! [B_139,C_140,D_141] :
      ( k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0(B_139),C_140,u1_struct_0(D_141)) = k2_tmap_1('#skF_2',B_139,C_140,D_141)
      | ~ m1_pre_topc(D_141,'#skF_2')
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_139))))
      | ~ v1_funct_2(C_140,k1_relat_1('#skF_4'),u1_struct_0(B_139))
      | ~ v1_funct_1(C_140)
      | ~ l1_pre_topc(B_139)
      | ~ v2_pre_topc(B_139)
      | v2_struct_0(B_139)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_179,c_179,c_410])).

tff(c_423,plain,(
    ! [B_142,C_143,D_144] :
      ( k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0(B_142),C_143,u1_struct_0(D_144)) = k2_tmap_1('#skF_2',B_142,C_143,D_144)
      | ~ m1_pre_topc(D_144,'#skF_2')
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_142))))
      | ~ v1_funct_2(C_143,k1_relat_1('#skF_4'),u1_struct_0(B_142))
      | ~ v1_funct_1(C_143)
      | ~ l1_pre_topc(B_142)
      | ~ v2_pre_topc(B_142)
      | v2_struct_0(B_142) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_418])).

tff(c_427,plain,(
    ! [D_144] :
      ( k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_144)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_144)
      | ~ m1_pre_topc(D_144,'#skF_2')
      | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_183,c_423])).

tff(c_434,plain,(
    ! [D_144] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_144)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_144)
      | ~ m1_pre_topc(D_144,'#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_48,c_184,c_266,c_427])).

tff(c_439,plain,(
    ! [D_145] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_145)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_145)
      | ~ m1_pre_topc(D_145,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_434])).

tff(c_448,plain,
    ( k7_relat_1('#skF_4',k1_relat_1('#skF_4')) = k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_290,c_439])).

tff(c_455,plain,(
    k7_relat_1('#skF_4',k1_relat_1('#skF_4')) = k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_448])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_96,plain,(
    ! [B_77,A_78] :
      ( k7_relat_1(B_77,A_78) = B_77
      | ~ r1_tarski(k1_relat_1(B_77),A_78)
      | ~ v1_relat_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_101,plain,(
    ! [B_77] :
      ( k7_relat_1(B_77,k1_relat_1(B_77)) = B_77
      | ~ v1_relat_1(B_77) ) ),
    inference(resolution,[status(thm)],[c_6,c_96])).

tff(c_459,plain,
    ( k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_455,c_101])).

tff(c_466,plain,(
    k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_459])).

tff(c_40,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_198,plain,(
    ~ r1_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_40])).

tff(c_294,plain,(
    ~ r1_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_198])).

tff(c_471,plain,(
    ~ r1_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_466,c_294])).

tff(c_505,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'))))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_1'))
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_401,c_471])).

tff(c_508,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_184,c_183,c_505])).

tff(c_510,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_402,c_508])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:20:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.70/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.37  
% 2.70/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.37  %$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.70/1.37  
% 2.70/1.37  %Foreground sorts:
% 2.70/1.37  
% 2.70/1.37  
% 2.70/1.37  %Background operators:
% 2.70/1.37  
% 2.70/1.37  
% 2.70/1.37  %Foreground operators:
% 2.70/1.37  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.70/1.37  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.70/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.70/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.70/1.37  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 2.70/1.37  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.70/1.37  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.70/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.70/1.37  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.70/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.70/1.37  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.70/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.70/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.70/1.37  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.70/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.70/1.37  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.70/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.70/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.70/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.70/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.70/1.37  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 2.70/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.70/1.37  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.70/1.37  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.70/1.37  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.70/1.37  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.70/1.37  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 2.70/1.37  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.70/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.70/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.70/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.70/1.37  
% 2.98/1.39  tff(f_180, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => r1_funct_2(u1_struct_0(B), u1_struct_0(A), u1_struct_0(C), u1_struct_0(A), D, k2_tmap_1(B, A, D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_tmap_1)).
% 2.98/1.39  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.98/1.39  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.98/1.39  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.98/1.39  tff(f_69, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 2.98/1.39  tff(f_61, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.98/1.39  tff(f_91, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.98/1.39  tff(f_120, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => r1_funct_2(A, B, C, D, E, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r1_funct_2)).
% 2.98/1.39  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 2.98/1.39  tff(f_100, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 2.98/1.39  tff(f_75, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.98/1.39  tff(f_147, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 2.98/1.39  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.98/1.39  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 2.98/1.39  tff(c_60, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_180])).
% 2.98/1.39  tff(c_26, plain, (![A_21]: (l1_struct_0(A_21) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.98/1.39  tff(c_64, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_180])).
% 2.98/1.39  tff(c_48, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_180])).
% 2.98/1.39  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_180])).
% 2.98/1.39  tff(c_69, plain, (![C_65, A_66, B_67]: (v1_relat_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.98/1.39  tff(c_73, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_69])).
% 2.98/1.39  tff(c_90, plain, (![C_73, A_74, B_75]: (v4_relat_1(C_73, A_74) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.98/1.39  tff(c_94, plain, (v4_relat_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_44, c_90])).
% 2.98/1.39  tff(c_112, plain, (![B_81, A_82]: (k1_relat_1(B_81)=A_82 | ~v1_partfun1(B_81, A_82) | ~v4_relat_1(B_81, A_82) | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.98/1.39  tff(c_115, plain, (u1_struct_0('#skF_2')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', u1_struct_0('#skF_2')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_94, c_112])).
% 2.98/1.39  tff(c_118, plain, (u1_struct_0('#skF_2')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_115])).
% 2.98/1.39  tff(c_119, plain, (~v1_partfun1('#skF_4', u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_118])).
% 2.98/1.39  tff(c_46, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_180])).
% 2.98/1.39  tff(c_158, plain, (![C_98, A_99, B_100]: (v1_partfun1(C_98, A_99) | ~v1_funct_2(C_98, A_99, B_100) | ~v1_funct_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))) | v1_xboole_0(B_100))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.98/1.39  tff(c_161, plain, (v1_partfun1('#skF_4', u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_158])).
% 2.98/1.39  tff(c_164, plain, (v1_partfun1('#skF_4', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_161])).
% 2.98/1.39  tff(c_165, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_119, c_164])).
% 2.98/1.39  tff(c_30, plain, (![A_23]: (~v1_xboole_0(u1_struct_0(A_23)) | ~l1_struct_0(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.98/1.39  tff(c_168, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_165, c_30])).
% 2.98/1.39  tff(c_171, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_64, c_168])).
% 2.98/1.39  tff(c_174, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_171])).
% 2.98/1.39  tff(c_178, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_174])).
% 2.98/1.39  tff(c_179, plain, (u1_struct_0('#skF_2')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_118])).
% 2.98/1.39  tff(c_184, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_46])).
% 2.98/1.39  tff(c_183, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_44])).
% 2.98/1.39  tff(c_345, plain, (![C_121, A_124, B_122, D_126, F_123, E_125]: (r1_funct_2(A_124, B_122, C_121, D_126, E_125, E_125) | ~m1_subset_1(F_123, k1_zfmisc_1(k2_zfmisc_1(C_121, D_126))) | ~v1_funct_2(F_123, C_121, D_126) | ~v1_funct_1(F_123) | ~m1_subset_1(E_125, k1_zfmisc_1(k2_zfmisc_1(A_124, B_122))) | ~v1_funct_2(E_125, A_124, B_122) | ~v1_funct_1(E_125) | v1_xboole_0(D_126) | v1_xboole_0(B_122))), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.98/1.39  tff(c_347, plain, (![A_124, B_122, E_125]: (r1_funct_2(A_124, B_122, k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), E_125, E_125) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_125, k1_zfmisc_1(k2_zfmisc_1(A_124, B_122))) | ~v1_funct_2(E_125, A_124, B_122) | ~v1_funct_1(E_125) | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_122))), inference(resolution, [status(thm)], [c_183, c_345])).
% 2.98/1.39  tff(c_350, plain, (![A_124, B_122, E_125]: (r1_funct_2(A_124, B_122, k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), E_125, E_125) | ~m1_subset_1(E_125, k1_zfmisc_1(k2_zfmisc_1(A_124, B_122))) | ~v1_funct_2(E_125, A_124, B_122) | ~v1_funct_1(E_125) | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_122))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_184, c_347])).
% 2.98/1.39  tff(c_368, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_350])).
% 2.98/1.39  tff(c_390, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_368, c_30])).
% 2.98/1.39  tff(c_393, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_64, c_390])).
% 2.98/1.39  tff(c_396, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_393])).
% 2.98/1.39  tff(c_400, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_396])).
% 2.98/1.39  tff(c_402, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_350])).
% 2.98/1.39  tff(c_401, plain, (![A_124, B_122, E_125]: (r1_funct_2(A_124, B_122, k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), E_125, E_125) | ~m1_subset_1(E_125, k1_zfmisc_1(k2_zfmisc_1(A_124, B_122))) | ~v1_funct_2(E_125, A_124, B_122) | ~v1_funct_1(E_125) | v1_xboole_0(B_122))), inference(splitRight, [status(thm)], [c_350])).
% 2.98/1.39  tff(c_50, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_180])).
% 2.98/1.39  tff(c_54, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_180])).
% 2.98/1.39  tff(c_28, plain, (![A_22]: (m1_subset_1(u1_pre_topc(A_22), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_22)))) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.98/1.39  tff(c_188, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(k1_relat_1('#skF_4')))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_179, c_28])).
% 2.98/1.39  tff(c_195, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(k1_relat_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_188])).
% 2.98/1.39  tff(c_42, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_180])).
% 2.98/1.39  tff(c_182, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_42])).
% 2.98/1.39  tff(c_34, plain, (![C_28, A_24, D_29, B_25]: (C_28=A_24 | g1_pre_topc(C_28, D_29)!=g1_pre_topc(A_24, B_25) | ~m1_subset_1(B_25, k1_zfmisc_1(k1_zfmisc_1(A_24))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.98/1.39  tff(c_283, plain, (![A_117, B_118]: (u1_struct_0('#skF_3')=A_117 | g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2'))!=g1_pre_topc(A_117, B_118) | ~m1_subset_1(B_118, k1_zfmisc_1(k1_zfmisc_1(A_117))))), inference(superposition, [status(thm), theory('equality')], [c_182, c_34])).
% 2.98/1.39  tff(c_290, plain, (u1_struct_0('#skF_3')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_195, c_283])).
% 2.98/1.39  tff(c_62, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_180])).
% 2.98/1.39  tff(c_261, plain, (![A_109, B_110, C_111, D_112]: (k2_partfun1(A_109, B_110, C_111, D_112)=k7_relat_1(C_111, D_112) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))) | ~v1_funct_1(C_111))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.98/1.39  tff(c_263, plain, (![D_112]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', D_112)=k7_relat_1('#skF_4', D_112) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_183, c_261])).
% 2.98/1.39  tff(c_266, plain, (![D_112]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', D_112)=k7_relat_1('#skF_4', D_112))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_263])).
% 2.98/1.39  tff(c_58, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_180])).
% 2.98/1.39  tff(c_56, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_180])).
% 2.98/1.39  tff(c_404, plain, (![A_138, B_139, C_140, D_141]: (k2_partfun1(u1_struct_0(A_138), u1_struct_0(B_139), C_140, u1_struct_0(D_141))=k2_tmap_1(A_138, B_139, C_140, D_141) | ~m1_pre_topc(D_141, A_138) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_138), u1_struct_0(B_139)))) | ~v1_funct_2(C_140, u1_struct_0(A_138), u1_struct_0(B_139)) | ~v1_funct_1(C_140) | ~l1_pre_topc(B_139) | ~v2_pre_topc(B_139) | v2_struct_0(B_139) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(cnfTransformation, [status(thm)], [f_147])).
% 2.98/1.39  tff(c_410, plain, (![B_139, C_140, D_141]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0(B_139), C_140, u1_struct_0(D_141))=k2_tmap_1('#skF_2', B_139, C_140, D_141) | ~m1_pre_topc(D_141, '#skF_2') | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_139)))) | ~v1_funct_2(C_140, u1_struct_0('#skF_2'), u1_struct_0(B_139)) | ~v1_funct_1(C_140) | ~l1_pre_topc(B_139) | ~v2_pre_topc(B_139) | v2_struct_0(B_139) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_179, c_404])).
% 2.98/1.39  tff(c_418, plain, (![B_139, C_140, D_141]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0(B_139), C_140, u1_struct_0(D_141))=k2_tmap_1('#skF_2', B_139, C_140, D_141) | ~m1_pre_topc(D_141, '#skF_2') | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_139)))) | ~v1_funct_2(C_140, k1_relat_1('#skF_4'), u1_struct_0(B_139)) | ~v1_funct_1(C_140) | ~l1_pre_topc(B_139) | ~v2_pre_topc(B_139) | v2_struct_0(B_139) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_179, c_179, c_410])).
% 2.98/1.39  tff(c_423, plain, (![B_142, C_143, D_144]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0(B_142), C_143, u1_struct_0(D_144))=k2_tmap_1('#skF_2', B_142, C_143, D_144) | ~m1_pre_topc(D_144, '#skF_2') | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_142)))) | ~v1_funct_2(C_143, k1_relat_1('#skF_4'), u1_struct_0(B_142)) | ~v1_funct_1(C_143) | ~l1_pre_topc(B_142) | ~v2_pre_topc(B_142) | v2_struct_0(B_142))), inference(negUnitSimplification, [status(thm)], [c_58, c_418])).
% 2.98/1.39  tff(c_427, plain, (![D_144]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_144))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_144) | ~m1_pre_topc(D_144, '#skF_2') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_183, c_423])).
% 2.98/1.39  tff(c_434, plain, (![D_144]: (k7_relat_1('#skF_4', u1_struct_0(D_144))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_144) | ~m1_pre_topc(D_144, '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_48, c_184, c_266, c_427])).
% 2.98/1.39  tff(c_439, plain, (![D_145]: (k7_relat_1('#skF_4', u1_struct_0(D_145))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_145) | ~m1_pre_topc(D_145, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_64, c_434])).
% 2.98/1.39  tff(c_448, plain, (k7_relat_1('#skF_4', k1_relat_1('#skF_4'))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_290, c_439])).
% 2.98/1.39  tff(c_455, plain, (k7_relat_1('#skF_4', k1_relat_1('#skF_4'))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_448])).
% 2.98/1.39  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.98/1.39  tff(c_96, plain, (![B_77, A_78]: (k7_relat_1(B_77, A_78)=B_77 | ~r1_tarski(k1_relat_1(B_77), A_78) | ~v1_relat_1(B_77))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.98/1.39  tff(c_101, plain, (![B_77]: (k7_relat_1(B_77, k1_relat_1(B_77))=B_77 | ~v1_relat_1(B_77))), inference(resolution, [status(thm)], [c_6, c_96])).
% 2.98/1.39  tff(c_459, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_455, c_101])).
% 2.98/1.39  tff(c_466, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_73, c_459])).
% 2.98/1.39  tff(c_40, plain, (~r1_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_180])).
% 2.98/1.39  tff(c_198, plain, (~r1_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_40])).
% 2.98/1.39  tff(c_294, plain, (~r1_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_290, c_198])).
% 2.98/1.39  tff(c_471, plain, (~r1_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_466, c_294])).
% 2.98/1.39  tff(c_505, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_401, c_471])).
% 2.98/1.39  tff(c_508, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_184, c_183, c_505])).
% 2.98/1.39  tff(c_510, plain, $false, inference(negUnitSimplification, [status(thm)], [c_402, c_508])).
% 2.98/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/1.39  
% 2.98/1.39  Inference rules
% 2.98/1.39  ----------------------
% 2.98/1.39  #Ref     : 7
% 2.98/1.39  #Sup     : 88
% 2.98/1.39  #Fact    : 0
% 2.98/1.39  #Define  : 0
% 2.98/1.39  #Split   : 4
% 2.98/1.39  #Chain   : 0
% 2.98/1.39  #Close   : 0
% 2.98/1.39  
% 2.98/1.39  Ordering : KBO
% 2.98/1.39  
% 2.98/1.39  Simplification rules
% 2.98/1.39  ----------------------
% 2.98/1.39  #Subsume      : 14
% 2.98/1.39  #Demod        : 102
% 2.98/1.39  #Tautology    : 47
% 2.98/1.39  #SimpNegUnit  : 19
% 2.98/1.39  #BackRed      : 11
% 2.98/1.39  
% 2.98/1.39  #Partial instantiations: 0
% 2.98/1.39  #Strategies tried      : 1
% 2.98/1.39  
% 2.98/1.39  Timing (in seconds)
% 2.98/1.39  ----------------------
% 2.98/1.40  Preprocessing        : 0.34
% 2.98/1.40  Parsing              : 0.18
% 2.98/1.40  CNF conversion       : 0.02
% 2.98/1.40  Main loop            : 0.29
% 2.98/1.40  Inferencing          : 0.10
% 2.98/1.40  Reduction            : 0.10
% 2.98/1.40  Demodulation         : 0.07
% 2.98/1.40  BG Simplification    : 0.02
% 2.98/1.40  Subsumption          : 0.05
% 2.98/1.40  Abstraction          : 0.01
% 2.98/1.40  MUC search           : 0.00
% 2.98/1.40  Cooper               : 0.00
% 2.98/1.40  Total                : 0.66
% 2.98/1.40  Index Insertion      : 0.00
% 2.98/1.40  Index Deletion       : 0.00
% 2.98/1.40  Index Matching       : 0.00
% 2.98/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
