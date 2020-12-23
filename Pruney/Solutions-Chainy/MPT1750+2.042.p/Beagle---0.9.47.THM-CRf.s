%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:57 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 689 expanded)
%              Number of leaves         :   37 ( 215 expanded)
%              Depth                    :   22
%              Number of atoms          :  237 (2679 expanded)
%              Number of equality atoms :   38 ( 887 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > r2_relset_1 > v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_162,negated_conjecture,(
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

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_82,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_102,axiom,(
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

tff(f_73,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_129,axiom,(
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

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r1_tarski(A,C)
       => r2_relset_1(A,B,k2_partfun1(A,B,D,C),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_funct_2)).

tff(f_39,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(c_52,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_18,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_40,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_46,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_20,plain,(
    ! [A_16] :
      ( m1_subset_1(u1_pre_topc(A_16),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_16))))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_34,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_90,plain,(
    ! [D_69,B_70,C_71,A_72] :
      ( D_69 = B_70
      | g1_pre_topc(C_71,D_69) != g1_pre_topc(A_72,B_70)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(k1_zfmisc_1(A_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_94,plain,(
    ! [D_69,C_71] :
      ( u1_pre_topc('#skF_2') = D_69
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(C_71,D_69)
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_90])).

tff(c_131,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_134,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_131])).

tff(c_138,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_134])).

tff(c_139,plain,(
    ! [D_69,C_71] :
      ( u1_pre_topc('#skF_2') = D_69
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(C_71,D_69) ) ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_157,plain,(
    u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_139])).

tff(c_140,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_172,plain,(
    m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_140])).

tff(c_173,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_3')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_34])).

tff(c_26,plain,(
    ! [C_22,A_18,D_23,B_19] :
      ( C_22 = A_18
      | g1_pre_topc(C_22,D_23) != g1_pre_topc(A_18,B_19)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(k1_zfmisc_1(A_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_203,plain,(
    ! [C_22,D_23] :
      ( u1_struct_0('#skF_2') = C_22
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(C_22,D_23)
      | ~ m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_26])).

tff(c_209,plain,(
    ! [C_22,D_23] :
      ( u1_struct_0('#skF_2') = C_22
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(C_22,D_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_203])).

tff(c_222,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_209])).

tff(c_38,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_236,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_38])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_235,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_36])).

tff(c_325,plain,(
    ! [C_121,B_122,F_124,D_126,E_123,A_125] :
      ( r1_funct_2(A_125,B_122,C_121,D_126,E_123,E_123)
      | ~ m1_subset_1(F_124,k1_zfmisc_1(k2_zfmisc_1(C_121,D_126)))
      | ~ v1_funct_2(F_124,C_121,D_126)
      | ~ v1_funct_1(F_124)
      | ~ m1_subset_1(E_123,k1_zfmisc_1(k2_zfmisc_1(A_125,B_122)))
      | ~ v1_funct_2(E_123,A_125,B_122)
      | ~ v1_funct_1(E_123)
      | v1_xboole_0(D_126)
      | v1_xboole_0(B_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_327,plain,(
    ! [A_125,B_122,E_123] :
      ( r1_funct_2(A_125,B_122,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),E_123,E_123)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_123,k1_zfmisc_1(k2_zfmisc_1(A_125,B_122)))
      | ~ v1_funct_2(E_123,A_125,B_122)
      | ~ v1_funct_1(E_123)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_122) ) ),
    inference(resolution,[status(thm)],[c_235,c_325])).

tff(c_332,plain,(
    ! [A_125,B_122,E_123] :
      ( r1_funct_2(A_125,B_122,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),E_123,E_123)
      | ~ m1_subset_1(E_123,k1_zfmisc_1(k2_zfmisc_1(A_125,B_122)))
      | ~ v1_funct_2(E_123,A_125,B_122)
      | ~ v1_funct_1(E_123)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_122) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_236,c_327])).

tff(c_378,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_332])).

tff(c_22,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0(u1_struct_0(A_17))
      | ~ l1_struct_0(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_381,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_378,c_22])).

tff(c_384,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_381])).

tff(c_387,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_384])).

tff(c_391,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_387])).

tff(c_393,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_332])).

tff(c_392,plain,(
    ! [A_125,B_122,E_123] :
      ( r1_funct_2(A_125,B_122,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),E_123,E_123)
      | ~ m1_subset_1(E_123,k1_zfmisc_1(k2_zfmisc_1(A_125,B_122)))
      | ~ v1_funct_2(E_123,A_125,B_122)
      | ~ v1_funct_1(E_123)
      | v1_xboole_0(B_122) ) ),
    inference(splitRight,[status(thm)],[c_332])).

tff(c_42,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_54,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_48,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_415,plain,(
    ! [A_143,B_144,C_145,D_146] :
      ( k2_partfun1(u1_struct_0(A_143),u1_struct_0(B_144),C_145,u1_struct_0(D_146)) = k2_tmap_1(A_143,B_144,C_145,D_146)
      | ~ m1_pre_topc(D_146,A_143)
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_143),u1_struct_0(B_144))))
      | ~ v1_funct_2(C_145,u1_struct_0(A_143),u1_struct_0(B_144))
      | ~ v1_funct_1(C_145)
      | ~ l1_pre_topc(B_144)
      | ~ v2_pre_topc(B_144)
      | v2_struct_0(B_144)
      | ~ l1_pre_topc(A_143)
      | ~ v2_pre_topc(A_143)
      | v2_struct_0(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_419,plain,(
    ! [B_144,C_145,D_146] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0(B_144),C_145,u1_struct_0(D_146)) = k2_tmap_1('#skF_2',B_144,C_145,D_146)
      | ~ m1_pre_topc(D_146,'#skF_2')
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_144))))
      | ~ v1_funct_2(C_145,u1_struct_0('#skF_2'),u1_struct_0(B_144))
      | ~ v1_funct_1(C_145)
      | ~ l1_pre_topc(B_144)
      | ~ v2_pre_topc(B_144)
      | v2_struct_0(B_144)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_415])).

tff(c_430,plain,(
    ! [B_144,C_145,D_146] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_144),C_145,u1_struct_0(D_146)) = k2_tmap_1('#skF_2',B_144,C_145,D_146)
      | ~ m1_pre_topc(D_146,'#skF_2')
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_144))))
      | ~ v1_funct_2(C_145,u1_struct_0('#skF_3'),u1_struct_0(B_144))
      | ~ v1_funct_1(C_145)
      | ~ l1_pre_topc(B_144)
      | ~ v2_pre_topc(B_144)
      | v2_struct_0(B_144)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_222,c_222,c_419])).

tff(c_436,plain,(
    ! [B_147,C_148,D_149] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_147),C_148,u1_struct_0(D_149)) = k2_tmap_1('#skF_2',B_147,C_148,D_149)
      | ~ m1_pre_topc(D_149,'#skF_2')
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_147))))
      | ~ v1_funct_2(C_148,u1_struct_0('#skF_3'),u1_struct_0(B_147))
      | ~ v1_funct_1(C_148)
      | ~ l1_pre_topc(B_147)
      | ~ v2_pre_topc(B_147)
      | v2_struct_0(B_147) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_430])).

tff(c_438,plain,(
    ! [D_149] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_149)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_149)
      | ~ m1_pre_topc(D_149,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_235,c_436])).

tff(c_446,plain,(
    ! [D_149] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_149)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_149)
      | ~ m1_pre_topc(D_149,'#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_40,c_236,c_438])).

tff(c_452,plain,(
    ! [D_150] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_150)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_150)
      | ~ m1_pre_topc(D_150,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_446])).

tff(c_12,plain,(
    ! [A_7,B_8,C_9,D_10] :
      ( m1_subset_1(k2_partfun1(A_7,B_8,C_9,D_10),k1_zfmisc_1(k2_zfmisc_1(A_7,B_8)))
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8)))
      | ~ v1_funct_1(C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_279,plain,(
    ! [A_102,B_103,D_104,C_105] :
      ( r2_relset_1(A_102,B_103,k2_partfun1(A_102,B_103,D_104,C_105),D_104)
      | ~ r1_tarski(A_102,C_105)
      | ~ m1_subset_1(D_104,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103)))
      | ~ v1_funct_2(D_104,A_102,B_103)
      | ~ v1_funct_1(D_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_281,plain,(
    ! [C_105] :
      ( r2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',C_105),'#skF_4')
      | ~ r1_tarski(u1_struct_0('#skF_3'),C_105)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_235,c_279])).

tff(c_296,plain,(
    ! [C_108] :
      ( r2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',C_108),'#skF_4')
      | ~ r1_tarski(u1_struct_0('#skF_3'),C_108) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_236,c_281])).

tff(c_10,plain,(
    ! [D_6,C_5,A_3,B_4] :
      ( D_6 = C_5
      | ~ r2_relset_1(A_3,B_4,C_5,D_6)
      | ~ m1_subset_1(D_6,k1_zfmisc_1(k2_zfmisc_1(A_3,B_4)))
      | ~ m1_subset_1(C_5,k1_zfmisc_1(k2_zfmisc_1(A_3,B_4))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_298,plain,(
    ! [C_108] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',C_108) = '#skF_4'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))))
      | ~ m1_subset_1(k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',C_108),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))))
      | ~ r1_tarski(u1_struct_0('#skF_3'),C_108) ) ),
    inference(resolution,[status(thm)],[c_296,c_10])).

tff(c_317,plain,(
    ! [C_120] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',C_120) = '#skF_4'
      | ~ m1_subset_1(k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',C_120),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))))
      | ~ r1_tarski(u1_struct_0('#skF_3'),C_120) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_298])).

tff(c_321,plain,(
    ! [D_10] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',D_10) = '#skF_4'
      | ~ r1_tarski(u1_struct_0('#skF_3'),D_10)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_12,c_317])).

tff(c_324,plain,(
    ! [D_10] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',D_10) = '#skF_4'
      | ~ r1_tarski(u1_struct_0('#skF_3'),D_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_235,c_321])).

tff(c_516,plain,(
    ! [D_154] :
      ( k2_tmap_1('#skF_2','#skF_1','#skF_4',D_154) = '#skF_4'
      | ~ r1_tarski(u1_struct_0('#skF_3'),u1_struct_0(D_154))
      | ~ m1_pre_topc(D_154,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_452,c_324])).

tff(c_523,plain,
    ( k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4'
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_516])).

tff(c_528,plain,(
    k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_523])).

tff(c_32,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_233,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_32])).

tff(c_529,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_528,c_233])).

tff(c_542,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_392,c_529])).

tff(c_545,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_236,c_235,c_542])).

tff(c_547,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_393,c_545])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:03:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.98/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/1.49  
% 2.98/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/1.49  %$ r1_funct_2 > r2_relset_1 > v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.98/1.49  
% 2.98/1.49  %Foreground sorts:
% 2.98/1.49  
% 2.98/1.49  
% 2.98/1.49  %Background operators:
% 2.98/1.49  
% 2.98/1.49  
% 2.98/1.49  %Foreground operators:
% 2.98/1.49  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.98/1.49  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.98/1.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.98/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.98/1.49  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.98/1.49  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 2.98/1.49  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.98/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.98/1.49  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.98/1.49  tff('#skF_2', type, '#skF_2': $i).
% 2.98/1.49  tff('#skF_3', type, '#skF_3': $i).
% 2.98/1.49  tff('#skF_1', type, '#skF_1': $i).
% 2.98/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.98/1.49  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.98/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.98/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.98/1.49  tff('#skF_4', type, '#skF_4': $i).
% 2.98/1.49  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 2.98/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.98/1.49  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.98/1.49  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.98/1.49  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.98/1.49  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 2.98/1.49  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.98/1.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.98/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.98/1.49  
% 2.98/1.51  tff(f_162, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => r1_funct_2(u1_struct_0(B), u1_struct_0(A), u1_struct_0(C), u1_struct_0(A), D, k2_tmap_1(B, A, D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_tmap_1)).
% 2.98/1.51  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.98/1.51  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 2.98/1.51  tff(f_82, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 2.98/1.51  tff(f_102, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => r1_funct_2(A, B, C, D, E, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r1_funct_2)).
% 2.98/1.51  tff(f_73, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.98/1.51  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.98/1.51  tff(f_129, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 2.98/1.51  tff(f_47, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 2.98/1.51  tff(f_57, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(A, C) => r2_relset_1(A, B, k2_partfun1(A, B, D, C), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_funct_2)).
% 2.98/1.51  tff(f_39, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.98/1.51  tff(c_52, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_162])).
% 2.98/1.51  tff(c_18, plain, (![A_15]: (l1_struct_0(A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.98/1.51  tff(c_56, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_162])).
% 2.98/1.51  tff(c_40, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_162])).
% 2.98/1.51  tff(c_46, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_162])).
% 2.98/1.51  tff(c_20, plain, (![A_16]: (m1_subset_1(u1_pre_topc(A_16), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_16)))) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.98/1.51  tff(c_34, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_162])).
% 2.98/1.51  tff(c_90, plain, (![D_69, B_70, C_71, A_72]: (D_69=B_70 | g1_pre_topc(C_71, D_69)!=g1_pre_topc(A_72, B_70) | ~m1_subset_1(B_70, k1_zfmisc_1(k1_zfmisc_1(A_72))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.98/1.51  tff(c_94, plain, (![D_69, C_71]: (u1_pre_topc('#skF_2')=D_69 | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=g1_pre_topc(C_71, D_69) | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))))), inference(superposition, [status(thm), theory('equality')], [c_34, c_90])).
% 2.98/1.51  tff(c_131, plain, (~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_94])).
% 2.98/1.51  tff(c_134, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_20, c_131])).
% 2.98/1.51  tff(c_138, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_134])).
% 2.98/1.51  tff(c_139, plain, (![D_69, C_71]: (u1_pre_topc('#skF_2')=D_69 | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=g1_pre_topc(C_71, D_69))), inference(splitRight, [status(thm)], [c_94])).
% 2.98/1.51  tff(c_157, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_139])).
% 2.98/1.51  tff(c_140, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_94])).
% 2.98/1.51  tff(c_172, plain, (m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_140])).
% 2.98/1.51  tff(c_173, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_3'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_34])).
% 2.98/1.51  tff(c_26, plain, (![C_22, A_18, D_23, B_19]: (C_22=A_18 | g1_pre_topc(C_22, D_23)!=g1_pre_topc(A_18, B_19) | ~m1_subset_1(B_19, k1_zfmisc_1(k1_zfmisc_1(A_18))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.98/1.51  tff(c_203, plain, (![C_22, D_23]: (u1_struct_0('#skF_2')=C_22 | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=g1_pre_topc(C_22, D_23) | ~m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))))), inference(superposition, [status(thm), theory('equality')], [c_173, c_26])).
% 2.98/1.51  tff(c_209, plain, (![C_22, D_23]: (u1_struct_0('#skF_2')=C_22 | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=g1_pre_topc(C_22, D_23))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_203])).
% 2.98/1.51  tff(c_222, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_209])).
% 2.98/1.51  tff(c_38, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_162])).
% 2.98/1.51  tff(c_236, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_222, c_38])).
% 2.98/1.51  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_162])).
% 2.98/1.51  tff(c_235, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_222, c_36])).
% 2.98/1.51  tff(c_325, plain, (![C_121, B_122, F_124, D_126, E_123, A_125]: (r1_funct_2(A_125, B_122, C_121, D_126, E_123, E_123) | ~m1_subset_1(F_124, k1_zfmisc_1(k2_zfmisc_1(C_121, D_126))) | ~v1_funct_2(F_124, C_121, D_126) | ~v1_funct_1(F_124) | ~m1_subset_1(E_123, k1_zfmisc_1(k2_zfmisc_1(A_125, B_122))) | ~v1_funct_2(E_123, A_125, B_122) | ~v1_funct_1(E_123) | v1_xboole_0(D_126) | v1_xboole_0(B_122))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.98/1.51  tff(c_327, plain, (![A_125, B_122, E_123]: (r1_funct_2(A_125, B_122, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), E_123, E_123) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_123, k1_zfmisc_1(k2_zfmisc_1(A_125, B_122))) | ~v1_funct_2(E_123, A_125, B_122) | ~v1_funct_1(E_123) | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_122))), inference(resolution, [status(thm)], [c_235, c_325])).
% 2.98/1.51  tff(c_332, plain, (![A_125, B_122, E_123]: (r1_funct_2(A_125, B_122, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), E_123, E_123) | ~m1_subset_1(E_123, k1_zfmisc_1(k2_zfmisc_1(A_125, B_122))) | ~v1_funct_2(E_123, A_125, B_122) | ~v1_funct_1(E_123) | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_122))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_236, c_327])).
% 2.98/1.51  tff(c_378, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_332])).
% 2.98/1.51  tff(c_22, plain, (![A_17]: (~v1_xboole_0(u1_struct_0(A_17)) | ~l1_struct_0(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.98/1.51  tff(c_381, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_378, c_22])).
% 2.98/1.51  tff(c_384, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_56, c_381])).
% 2.98/1.51  tff(c_387, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_384])).
% 2.98/1.51  tff(c_391, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_387])).
% 2.98/1.51  tff(c_393, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_332])).
% 2.98/1.51  tff(c_392, plain, (![A_125, B_122, E_123]: (r1_funct_2(A_125, B_122, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), E_123, E_123) | ~m1_subset_1(E_123, k1_zfmisc_1(k2_zfmisc_1(A_125, B_122))) | ~v1_funct_2(E_123, A_125, B_122) | ~v1_funct_1(E_123) | v1_xboole_0(B_122))), inference(splitRight, [status(thm)], [c_332])).
% 2.98/1.51  tff(c_42, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_162])).
% 2.98/1.51  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.98/1.51  tff(c_54, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_162])).
% 2.98/1.51  tff(c_50, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_162])).
% 2.98/1.51  tff(c_48, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_162])).
% 2.98/1.51  tff(c_415, plain, (![A_143, B_144, C_145, D_146]: (k2_partfun1(u1_struct_0(A_143), u1_struct_0(B_144), C_145, u1_struct_0(D_146))=k2_tmap_1(A_143, B_144, C_145, D_146) | ~m1_pre_topc(D_146, A_143) | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_143), u1_struct_0(B_144)))) | ~v1_funct_2(C_145, u1_struct_0(A_143), u1_struct_0(B_144)) | ~v1_funct_1(C_145) | ~l1_pre_topc(B_144) | ~v2_pre_topc(B_144) | v2_struct_0(B_144) | ~l1_pre_topc(A_143) | ~v2_pre_topc(A_143) | v2_struct_0(A_143))), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.98/1.51  tff(c_419, plain, (![B_144, C_145, D_146]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0(B_144), C_145, u1_struct_0(D_146))=k2_tmap_1('#skF_2', B_144, C_145, D_146) | ~m1_pre_topc(D_146, '#skF_2') | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_144)))) | ~v1_funct_2(C_145, u1_struct_0('#skF_2'), u1_struct_0(B_144)) | ~v1_funct_1(C_145) | ~l1_pre_topc(B_144) | ~v2_pre_topc(B_144) | v2_struct_0(B_144) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_222, c_415])).
% 2.98/1.51  tff(c_430, plain, (![B_144, C_145, D_146]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_144), C_145, u1_struct_0(D_146))=k2_tmap_1('#skF_2', B_144, C_145, D_146) | ~m1_pre_topc(D_146, '#skF_2') | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_144)))) | ~v1_funct_2(C_145, u1_struct_0('#skF_3'), u1_struct_0(B_144)) | ~v1_funct_1(C_145) | ~l1_pre_topc(B_144) | ~v2_pre_topc(B_144) | v2_struct_0(B_144) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_222, c_222, c_419])).
% 2.98/1.51  tff(c_436, plain, (![B_147, C_148, D_149]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_147), C_148, u1_struct_0(D_149))=k2_tmap_1('#skF_2', B_147, C_148, D_149) | ~m1_pre_topc(D_149, '#skF_2') | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_147)))) | ~v1_funct_2(C_148, u1_struct_0('#skF_3'), u1_struct_0(B_147)) | ~v1_funct_1(C_148) | ~l1_pre_topc(B_147) | ~v2_pre_topc(B_147) | v2_struct_0(B_147))), inference(negUnitSimplification, [status(thm)], [c_50, c_430])).
% 2.98/1.51  tff(c_438, plain, (![D_149]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_149))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_149) | ~m1_pre_topc(D_149, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_235, c_436])).
% 2.98/1.51  tff(c_446, plain, (![D_149]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_149))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_149) | ~m1_pre_topc(D_149, '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_40, c_236, c_438])).
% 2.98/1.51  tff(c_452, plain, (![D_150]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_150))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_150) | ~m1_pre_topc(D_150, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_56, c_446])).
% 2.98/1.51  tff(c_12, plain, (![A_7, B_8, C_9, D_10]: (m1_subset_1(k2_partfun1(A_7, B_8, C_9, D_10), k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))) | ~v1_funct_1(C_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.98/1.51  tff(c_279, plain, (![A_102, B_103, D_104, C_105]: (r2_relset_1(A_102, B_103, k2_partfun1(A_102, B_103, D_104, C_105), D_104) | ~r1_tarski(A_102, C_105) | ~m1_subset_1(D_104, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))) | ~v1_funct_2(D_104, A_102, B_103) | ~v1_funct_1(D_104))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.98/1.51  tff(c_281, plain, (![C_105]: (r2_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', C_105), '#skF_4') | ~r1_tarski(u1_struct_0('#skF_3'), C_105) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_235, c_279])).
% 2.98/1.51  tff(c_296, plain, (![C_108]: (r2_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', C_108), '#skF_4') | ~r1_tarski(u1_struct_0('#skF_3'), C_108))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_236, c_281])).
% 2.98/1.51  tff(c_10, plain, (![D_6, C_5, A_3, B_4]: (D_6=C_5 | ~r2_relset_1(A_3, B_4, C_5, D_6) | ~m1_subset_1(D_6, k1_zfmisc_1(k2_zfmisc_1(A_3, B_4))) | ~m1_subset_1(C_5, k1_zfmisc_1(k2_zfmisc_1(A_3, B_4))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.98/1.51  tff(c_298, plain, (![C_108]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', C_108)='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))) | ~m1_subset_1(k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', C_108), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))) | ~r1_tarski(u1_struct_0('#skF_3'), C_108))), inference(resolution, [status(thm)], [c_296, c_10])).
% 2.98/1.51  tff(c_317, plain, (![C_120]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', C_120)='#skF_4' | ~m1_subset_1(k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', C_120), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))) | ~r1_tarski(u1_struct_0('#skF_3'), C_120))), inference(demodulation, [status(thm), theory('equality')], [c_235, c_298])).
% 2.98/1.51  tff(c_321, plain, (![D_10]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', D_10)='#skF_4' | ~r1_tarski(u1_struct_0('#skF_3'), D_10) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_12, c_317])).
% 2.98/1.51  tff(c_324, plain, (![D_10]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', D_10)='#skF_4' | ~r1_tarski(u1_struct_0('#skF_3'), D_10))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_235, c_321])).
% 2.98/1.51  tff(c_516, plain, (![D_154]: (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_154)='#skF_4' | ~r1_tarski(u1_struct_0('#skF_3'), u1_struct_0(D_154)) | ~m1_pre_topc(D_154, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_452, c_324])).
% 2.98/1.51  tff(c_523, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4' | ~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_6, c_516])).
% 2.98/1.51  tff(c_528, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_523])).
% 2.98/1.51  tff(c_32, plain, (~r1_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_162])).
% 2.98/1.51  tff(c_233, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_222, c_32])).
% 2.98/1.51  tff(c_529, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_528, c_233])).
% 2.98/1.51  tff(c_542, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_392, c_529])).
% 2.98/1.51  tff(c_545, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_236, c_235, c_542])).
% 2.98/1.51  tff(c_547, plain, $false, inference(negUnitSimplification, [status(thm)], [c_393, c_545])).
% 2.98/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/1.51  
% 2.98/1.51  Inference rules
% 2.98/1.51  ----------------------
% 2.98/1.51  #Ref     : 7
% 2.98/1.51  #Sup     : 95
% 2.98/1.51  #Fact    : 0
% 2.98/1.51  #Define  : 0
% 2.98/1.51  #Split   : 5
% 2.98/1.51  #Chain   : 0
% 2.98/1.51  #Close   : 0
% 2.98/1.51  
% 2.98/1.51  Ordering : KBO
% 2.98/1.51  
% 2.98/1.51  Simplification rules
% 2.98/1.51  ----------------------
% 2.98/1.51  #Subsume      : 13
% 2.98/1.51  #Demod        : 113
% 2.98/1.51  #Tautology    : 42
% 2.98/1.51  #SimpNegUnit  : 8
% 2.98/1.51  #BackRed      : 11
% 2.98/1.51  
% 2.98/1.51  #Partial instantiations: 0
% 2.98/1.51  #Strategies tried      : 1
% 2.98/1.51  
% 2.98/1.51  Timing (in seconds)
% 2.98/1.51  ----------------------
% 2.98/1.52  Preprocessing        : 0.36
% 2.98/1.52  Parsing              : 0.21
% 2.98/1.52  CNF conversion       : 0.03
% 2.98/1.52  Main loop            : 0.32
% 2.98/1.52  Inferencing          : 0.11
% 2.98/1.52  Reduction            : 0.10
% 2.98/1.52  Demodulation         : 0.07
% 2.98/1.52  BG Simplification    : 0.02
% 2.98/1.52  Subsumption          : 0.06
% 2.98/1.52  Abstraction          : 0.02
% 2.98/1.52  MUC search           : 0.00
% 2.98/1.52  Cooper               : 0.00
% 2.98/1.52  Total                : 0.72
% 2.98/1.52  Index Insertion      : 0.00
% 2.98/1.52  Index Deletion       : 0.00
% 2.98/1.52  Index Matching       : 0.00
% 2.98/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
