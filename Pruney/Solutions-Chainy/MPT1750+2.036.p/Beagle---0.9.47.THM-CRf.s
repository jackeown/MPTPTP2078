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
% DateTime   : Thu Dec  3 10:26:56 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 256 expanded)
%              Number of leaves         :   43 ( 100 expanded)
%              Depth                    :   16
%              Number of atoms          :  221 (1036 expanded)
%              Number of equality atoms :   34 ( 218 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_165,negated_conjecture,(
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

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_83,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_105,axiom,(
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

tff(f_74,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_132,axiom,(
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

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(c_54,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_18,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_48,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_20,plain,(
    ! [A_18] :
      ( m1_subset_1(u1_pre_topc(A_18),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_18))))
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_36,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_124,plain,(
    ! [C_84,A_85,D_86,B_87] :
      ( C_84 = A_85
      | g1_pre_topc(C_84,D_86) != g1_pre_topc(A_85,B_87)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(k1_zfmisc_1(A_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_128,plain,(
    ! [C_84,D_86] :
      ( u1_struct_0('#skF_2') = C_84
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(C_84,D_86)
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_124])).

tff(c_172,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_175,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_172])).

tff(c_179,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_175])).

tff(c_180,plain,(
    ! [C_84,D_86] :
      ( u1_struct_0('#skF_2') = C_84
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(C_84,D_86) ) ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_203,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_180])).

tff(c_42,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_40,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_154,plain,(
    ! [B_98,A_99,C_101,D_97,F_100] :
      ( r1_funct_2(A_99,B_98,C_101,D_97,F_100,F_100)
      | ~ m1_subset_1(F_100,k1_zfmisc_1(k2_zfmisc_1(C_101,D_97)))
      | ~ v1_funct_2(F_100,C_101,D_97)
      | ~ m1_subset_1(F_100,k1_zfmisc_1(k2_zfmisc_1(A_99,B_98)))
      | ~ v1_funct_2(F_100,A_99,B_98)
      | ~ v1_funct_1(F_100)
      | v1_xboole_0(D_97)
      | v1_xboole_0(B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_156,plain,(
    ! [A_99,B_98] :
      ( r1_funct_2(A_99,B_98,u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_99,B_98)))
      | ~ v1_funct_2('#skF_4',A_99,B_98)
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_98) ) ),
    inference(resolution,[status(thm)],[c_38,c_154])).

tff(c_159,plain,(
    ! [A_99,B_98] :
      ( r1_funct_2(A_99,B_98,u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_99,B_98)))
      | ~ v1_funct_2('#skF_4',A_99,B_98)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_156])).

tff(c_389,plain,(
    ! [A_99,B_98] :
      ( r1_funct_2(A_99,B_98,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_99,B_98)))
      | ~ v1_funct_2('#skF_4',A_99,B_98)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_159])).

tff(c_390,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_389])).

tff(c_22,plain,(
    ! [A_19] :
      ( ~ v1_xboole_0(u1_struct_0(A_19))
      | ~ l1_struct_0(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_393,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_390,c_22])).

tff(c_396,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_393])).

tff(c_399,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_396])).

tff(c_403,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_399])).

tff(c_405,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_389])).

tff(c_220,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_40])).

tff(c_219,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_38])).

tff(c_404,plain,(
    ! [A_99,B_98] :
      ( r1_funct_2(A_99,B_98,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_99,B_98)))
      | ~ v1_funct_2('#skF_4',A_99,B_98)
      | v1_xboole_0(B_98) ) ),
    inference(splitRight,[status(thm)],[c_389])).

tff(c_44,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_56,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_129,plain,(
    ! [A_88,B_89,C_90,D_91] :
      ( k2_partfun1(A_88,B_89,C_90,D_91) = k7_relat_1(C_90,D_91)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89)))
      | ~ v1_funct_1(C_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_131,plain,(
    ! [D_91] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_91) = k7_relat_1('#skF_4',D_91)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_38,c_129])).

tff(c_134,plain,(
    ! [D_91] : k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_91) = k7_relat_1('#skF_4',D_91) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_131])).

tff(c_214,plain,(
    ! [D_91] : k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',D_91) = k7_relat_1('#skF_4',D_91) ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_134])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_50,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_266,plain,(
    ! [A_111,B_112,C_113,D_114] :
      ( k2_partfun1(u1_struct_0(A_111),u1_struct_0(B_112),C_113,u1_struct_0(D_114)) = k2_tmap_1(A_111,B_112,C_113,D_114)
      | ~ m1_pre_topc(D_114,A_111)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_111),u1_struct_0(B_112))))
      | ~ v1_funct_2(C_113,u1_struct_0(A_111),u1_struct_0(B_112))
      | ~ v1_funct_1(C_113)
      | ~ l1_pre_topc(B_112)
      | ~ v2_pre_topc(B_112)
      | v2_struct_0(B_112)
      | ~ l1_pre_topc(A_111)
      | ~ v2_pre_topc(A_111)
      | v2_struct_0(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_268,plain,(
    ! [B_112,C_113,D_114] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0(B_112),C_113,u1_struct_0(D_114)) = k2_tmap_1('#skF_2',B_112,C_113,D_114)
      | ~ m1_pre_topc(D_114,'#skF_2')
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_112))))
      | ~ v1_funct_2(C_113,u1_struct_0('#skF_2'),u1_struct_0(B_112))
      | ~ v1_funct_1(C_113)
      | ~ l1_pre_topc(B_112)
      | ~ v2_pre_topc(B_112)
      | v2_struct_0(B_112)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_266])).

tff(c_272,plain,(
    ! [B_112,C_113,D_114] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_112),C_113,u1_struct_0(D_114)) = k2_tmap_1('#skF_2',B_112,C_113,D_114)
      | ~ m1_pre_topc(D_114,'#skF_2')
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_112))))
      | ~ v1_funct_2(C_113,u1_struct_0('#skF_3'),u1_struct_0(B_112))
      | ~ v1_funct_1(C_113)
      | ~ l1_pre_topc(B_112)
      | ~ v2_pre_topc(B_112)
      | v2_struct_0(B_112)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_203,c_203,c_268])).

tff(c_414,plain,(
    ! [B_124,C_125,D_126] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_124),C_125,u1_struct_0(D_126)) = k2_tmap_1('#skF_2',B_124,C_125,D_126)
      | ~ m1_pre_topc(D_126,'#skF_2')
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_124))))
      | ~ v1_funct_2(C_125,u1_struct_0('#skF_3'),u1_struct_0(B_124))
      | ~ v1_funct_1(C_125)
      | ~ l1_pre_topc(B_124)
      | ~ v2_pre_topc(B_124)
      | v2_struct_0(B_124) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_272])).

tff(c_416,plain,(
    ! [D_126] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_126)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_126)
      | ~ m1_pre_topc(D_126,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_219,c_414])).

tff(c_421,plain,(
    ! [D_126] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_126)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_126)
      | ~ m1_pre_topc(D_126,'#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_42,c_220,c_214,c_416])).

tff(c_426,plain,(
    ! [D_127] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_127)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_127)
      | ~ m1_pre_topc(D_127,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_421])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_62,plain,(
    ! [B_62,A_63] :
      ( v1_relat_1(B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_63))
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_65,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_38,c_62])).

tff(c_68,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_65])).

tff(c_74,plain,(
    ! [C_67,A_68,B_69] :
      ( v4_relat_1(C_67,A_68)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_78,plain,(
    v4_relat_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_74])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k1_relat_1(B_5),A_4)
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_95,plain,(
    ! [B_76,A_77] :
      ( k7_relat_1(B_76,A_77) = B_76
      | ~ r1_tarski(k1_relat_1(B_76),A_77)
      | ~ v1_relat_1(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_100,plain,(
    ! [B_78,A_79] :
      ( k7_relat_1(B_78,A_79) = B_78
      | ~ v4_relat_1(B_78,A_79)
      | ~ v1_relat_1(B_78) ) ),
    inference(resolution,[status(thm)],[c_6,c_95])).

tff(c_103,plain,
    ( k7_relat_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_100])).

tff(c_106,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_103])).

tff(c_216,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_106])).

tff(c_432,plain,
    ( k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4'
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_426,c_216])).

tff(c_444,plain,(
    k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_432])).

tff(c_34,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_215,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_34])).

tff(c_449,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_444,c_215])).

tff(c_459,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_404,c_449])).

tff(c_462,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_219,c_459])).

tff(c_464,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_405,c_462])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:09:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.73/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.36  
% 2.73/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.36  %$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.81/1.36  
% 2.81/1.36  %Foreground sorts:
% 2.81/1.36  
% 2.81/1.36  
% 2.81/1.36  %Background operators:
% 2.81/1.36  
% 2.81/1.36  
% 2.81/1.36  %Foreground operators:
% 2.81/1.36  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.81/1.36  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.81/1.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.81/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.81/1.36  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 2.81/1.36  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.81/1.36  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.81/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.81/1.36  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.81/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.81/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.81/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.81/1.36  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.81/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.81/1.36  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.81/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.81/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.81/1.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.81/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.81/1.36  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 2.81/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.81/1.36  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.81/1.36  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.81/1.36  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.81/1.36  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.81/1.36  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 2.81/1.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.81/1.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.81/1.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.81/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.81/1.36  
% 2.81/1.38  tff(f_165, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => r1_funct_2(u1_struct_0(B), u1_struct_0(A), u1_struct_0(C), u1_struct_0(A), D, k2_tmap_1(B, A, D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_tmap_1)).
% 2.81/1.38  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.81/1.38  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 2.81/1.38  tff(f_83, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 2.81/1.38  tff(f_105, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (r1_funct_2(A, B, C, D, E, F) <=> (E = F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 2.81/1.38  tff(f_74, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.81/1.38  tff(f_58, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.81/1.38  tff(f_132, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 2.81/1.38  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.81/1.38  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.81/1.38  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.81/1.38  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.81/1.38  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 2.81/1.38  tff(c_54, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_165])).
% 2.81/1.38  tff(c_18, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.81/1.38  tff(c_58, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_165])).
% 2.81/1.38  tff(c_48, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_165])).
% 2.81/1.38  tff(c_20, plain, (![A_18]: (m1_subset_1(u1_pre_topc(A_18), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_18)))) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.81/1.38  tff(c_36, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_165])).
% 2.81/1.38  tff(c_124, plain, (![C_84, A_85, D_86, B_87]: (C_84=A_85 | g1_pre_topc(C_84, D_86)!=g1_pre_topc(A_85, B_87) | ~m1_subset_1(B_87, k1_zfmisc_1(k1_zfmisc_1(A_85))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.81/1.38  tff(c_128, plain, (![C_84, D_86]: (u1_struct_0('#skF_2')=C_84 | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=g1_pre_topc(C_84, D_86) | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))))), inference(superposition, [status(thm), theory('equality')], [c_36, c_124])).
% 2.81/1.38  tff(c_172, plain, (~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_128])).
% 2.81/1.38  tff(c_175, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_20, c_172])).
% 2.81/1.38  tff(c_179, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_175])).
% 2.81/1.38  tff(c_180, plain, (![C_84, D_86]: (u1_struct_0('#skF_2')=C_84 | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=g1_pre_topc(C_84, D_86))), inference(splitRight, [status(thm)], [c_128])).
% 2.81/1.38  tff(c_203, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_180])).
% 2.81/1.38  tff(c_42, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_165])).
% 2.81/1.38  tff(c_40, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_165])).
% 2.81/1.38  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_165])).
% 2.81/1.38  tff(c_154, plain, (![B_98, A_99, C_101, D_97, F_100]: (r1_funct_2(A_99, B_98, C_101, D_97, F_100, F_100) | ~m1_subset_1(F_100, k1_zfmisc_1(k2_zfmisc_1(C_101, D_97))) | ~v1_funct_2(F_100, C_101, D_97) | ~m1_subset_1(F_100, k1_zfmisc_1(k2_zfmisc_1(A_99, B_98))) | ~v1_funct_2(F_100, A_99, B_98) | ~v1_funct_1(F_100) | v1_xboole_0(D_97) | v1_xboole_0(B_98))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.81/1.38  tff(c_156, plain, (![A_99, B_98]: (r1_funct_2(A_99, B_98, u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_99, B_98))) | ~v1_funct_2('#skF_4', A_99, B_98) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_98))), inference(resolution, [status(thm)], [c_38, c_154])).
% 2.81/1.38  tff(c_159, plain, (![A_99, B_98]: (r1_funct_2(A_99, B_98, u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_99, B_98))) | ~v1_funct_2('#skF_4', A_99, B_98) | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_98))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_156])).
% 2.81/1.38  tff(c_389, plain, (![A_99, B_98]: (r1_funct_2(A_99, B_98, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_99, B_98))) | ~v1_funct_2('#skF_4', A_99, B_98) | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_98))), inference(demodulation, [status(thm), theory('equality')], [c_203, c_159])).
% 2.81/1.38  tff(c_390, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_389])).
% 2.81/1.38  tff(c_22, plain, (![A_19]: (~v1_xboole_0(u1_struct_0(A_19)) | ~l1_struct_0(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.81/1.38  tff(c_393, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_390, c_22])).
% 2.81/1.38  tff(c_396, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_58, c_393])).
% 2.81/1.38  tff(c_399, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_396])).
% 2.81/1.38  tff(c_403, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_399])).
% 2.81/1.38  tff(c_405, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_389])).
% 2.81/1.38  tff(c_220, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_203, c_40])).
% 2.81/1.38  tff(c_219, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_203, c_38])).
% 2.81/1.38  tff(c_404, plain, (![A_99, B_98]: (r1_funct_2(A_99, B_98, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_99, B_98))) | ~v1_funct_2('#skF_4', A_99, B_98) | v1_xboole_0(B_98))), inference(splitRight, [status(thm)], [c_389])).
% 2.81/1.38  tff(c_44, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_165])).
% 2.81/1.38  tff(c_56, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_165])).
% 2.81/1.38  tff(c_129, plain, (![A_88, B_89, C_90, D_91]: (k2_partfun1(A_88, B_89, C_90, D_91)=k7_relat_1(C_90, D_91) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))) | ~v1_funct_1(C_90))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.81/1.38  tff(c_131, plain, (![D_91]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_91)=k7_relat_1('#skF_4', D_91) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_38, c_129])).
% 2.81/1.38  tff(c_134, plain, (![D_91]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_91)=k7_relat_1('#skF_4', D_91))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_131])).
% 2.81/1.38  tff(c_214, plain, (![D_91]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', D_91)=k7_relat_1('#skF_4', D_91))), inference(demodulation, [status(thm), theory('equality')], [c_203, c_134])).
% 2.81/1.38  tff(c_52, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_165])).
% 2.81/1.38  tff(c_50, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_165])).
% 2.81/1.38  tff(c_266, plain, (![A_111, B_112, C_113, D_114]: (k2_partfun1(u1_struct_0(A_111), u1_struct_0(B_112), C_113, u1_struct_0(D_114))=k2_tmap_1(A_111, B_112, C_113, D_114) | ~m1_pre_topc(D_114, A_111) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_111), u1_struct_0(B_112)))) | ~v1_funct_2(C_113, u1_struct_0(A_111), u1_struct_0(B_112)) | ~v1_funct_1(C_113) | ~l1_pre_topc(B_112) | ~v2_pre_topc(B_112) | v2_struct_0(B_112) | ~l1_pre_topc(A_111) | ~v2_pre_topc(A_111) | v2_struct_0(A_111))), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.81/1.38  tff(c_268, plain, (![B_112, C_113, D_114]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0(B_112), C_113, u1_struct_0(D_114))=k2_tmap_1('#skF_2', B_112, C_113, D_114) | ~m1_pre_topc(D_114, '#skF_2') | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_112)))) | ~v1_funct_2(C_113, u1_struct_0('#skF_2'), u1_struct_0(B_112)) | ~v1_funct_1(C_113) | ~l1_pre_topc(B_112) | ~v2_pre_topc(B_112) | v2_struct_0(B_112) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_203, c_266])).
% 2.81/1.38  tff(c_272, plain, (![B_112, C_113, D_114]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_112), C_113, u1_struct_0(D_114))=k2_tmap_1('#skF_2', B_112, C_113, D_114) | ~m1_pre_topc(D_114, '#skF_2') | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_112)))) | ~v1_funct_2(C_113, u1_struct_0('#skF_3'), u1_struct_0(B_112)) | ~v1_funct_1(C_113) | ~l1_pre_topc(B_112) | ~v2_pre_topc(B_112) | v2_struct_0(B_112) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_203, c_203, c_268])).
% 2.81/1.38  tff(c_414, plain, (![B_124, C_125, D_126]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_124), C_125, u1_struct_0(D_126))=k2_tmap_1('#skF_2', B_124, C_125, D_126) | ~m1_pre_topc(D_126, '#skF_2') | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_124)))) | ~v1_funct_2(C_125, u1_struct_0('#skF_3'), u1_struct_0(B_124)) | ~v1_funct_1(C_125) | ~l1_pre_topc(B_124) | ~v2_pre_topc(B_124) | v2_struct_0(B_124))), inference(negUnitSimplification, [status(thm)], [c_52, c_272])).
% 2.81/1.38  tff(c_416, plain, (![D_126]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_126))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_126) | ~m1_pre_topc(D_126, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_219, c_414])).
% 2.81/1.38  tff(c_421, plain, (![D_126]: (k7_relat_1('#skF_4', u1_struct_0(D_126))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_126) | ~m1_pre_topc(D_126, '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_42, c_220, c_214, c_416])).
% 2.81/1.38  tff(c_426, plain, (![D_127]: (k7_relat_1('#skF_4', u1_struct_0(D_127))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_127) | ~m1_pre_topc(D_127, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_58, c_421])).
% 2.81/1.38  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.81/1.38  tff(c_62, plain, (![B_62, A_63]: (v1_relat_1(B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(A_63)) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.81/1.38  tff(c_65, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_38, c_62])).
% 2.81/1.38  tff(c_68, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_65])).
% 2.81/1.38  tff(c_74, plain, (![C_67, A_68, B_69]: (v4_relat_1(C_67, A_68) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.81/1.38  tff(c_78, plain, (v4_relat_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_74])).
% 2.81/1.38  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k1_relat_1(B_5), A_4) | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.81/1.38  tff(c_95, plain, (![B_76, A_77]: (k7_relat_1(B_76, A_77)=B_76 | ~r1_tarski(k1_relat_1(B_76), A_77) | ~v1_relat_1(B_76))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.81/1.38  tff(c_100, plain, (![B_78, A_79]: (k7_relat_1(B_78, A_79)=B_78 | ~v4_relat_1(B_78, A_79) | ~v1_relat_1(B_78))), inference(resolution, [status(thm)], [c_6, c_95])).
% 2.81/1.38  tff(c_103, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_2'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_78, c_100])).
% 2.81/1.38  tff(c_106, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_2'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_103])).
% 2.81/1.38  tff(c_216, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_203, c_106])).
% 2.81/1.38  tff(c_432, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4' | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_426, c_216])).
% 2.81/1.38  tff(c_444, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_432])).
% 2.81/1.38  tff(c_34, plain, (~r1_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_165])).
% 2.81/1.38  tff(c_215, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_203, c_34])).
% 2.81/1.38  tff(c_449, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_444, c_215])).
% 2.81/1.38  tff(c_459, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_404, c_449])).
% 2.81/1.38  tff(c_462, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_220, c_219, c_459])).
% 2.81/1.38  tff(c_464, plain, $false, inference(negUnitSimplification, [status(thm)], [c_405, c_462])).
% 2.81/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.38  
% 2.81/1.38  Inference rules
% 2.81/1.38  ----------------------
% 2.81/1.38  #Ref     : 7
% 2.81/1.38  #Sup     : 74
% 2.81/1.38  #Fact    : 0
% 2.81/1.38  #Define  : 0
% 2.81/1.38  #Split   : 6
% 2.81/1.38  #Chain   : 0
% 2.81/1.38  #Close   : 0
% 2.81/1.38  
% 2.81/1.38  Ordering : KBO
% 2.81/1.38  
% 2.81/1.38  Simplification rules
% 2.81/1.38  ----------------------
% 2.81/1.38  #Subsume      : 14
% 2.81/1.38  #Demod        : 79
% 2.81/1.38  #Tautology    : 42
% 2.81/1.38  #SimpNegUnit  : 10
% 2.81/1.38  #BackRed      : 13
% 2.81/1.38  
% 2.81/1.38  #Partial instantiations: 0
% 2.81/1.38  #Strategies tried      : 1
% 2.81/1.38  
% 2.81/1.38  Timing (in seconds)
% 2.81/1.38  ----------------------
% 2.81/1.38  Preprocessing        : 0.33
% 2.81/1.38  Parsing              : 0.18
% 2.81/1.38  CNF conversion       : 0.02
% 2.81/1.38  Main loop            : 0.27
% 2.81/1.38  Inferencing          : 0.10
% 2.81/1.38  Reduction            : 0.09
% 2.81/1.38  Demodulation         : 0.06
% 2.81/1.38  BG Simplification    : 0.02
% 2.81/1.39  Subsumption          : 0.05
% 2.81/1.39  Abstraction          : 0.01
% 2.81/1.39  MUC search           : 0.00
% 2.81/1.39  Cooper               : 0.00
% 2.81/1.39  Total                : 0.64
% 2.81/1.39  Index Insertion      : 0.00
% 2.81/1.39  Index Deletion       : 0.00
% 2.81/1.39  Index Matching       : 0.00
% 2.81/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
