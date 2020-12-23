%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:56 EST 2020

% Result     : Theorem 2.54s
% Output     : CNFRefutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 264 expanded)
%              Number of leaves         :   40 ( 101 expanded)
%              Depth                    :   16
%              Number of atoms          :  221 (1078 expanded)
%              Number of equality atoms :   37 ( 235 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_159,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_tmap_1)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_77,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_99,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

tff(f_68,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_126,axiom,(
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

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(c_50,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_14,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_44,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_16,plain,(
    ! [A_16] :
      ( m1_subset_1(u1_pre_topc(A_16),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_16))))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_32,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_109,plain,(
    ! [D_76,B_77,C_78,A_79] :
      ( D_76 = B_77
      | g1_pre_topc(C_78,D_76) != g1_pre_topc(A_79,B_77)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(k1_zfmisc_1(A_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_113,plain,(
    ! [D_76,C_78] :
      ( u1_pre_topc('#skF_2') = D_76
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(C_78,D_76)
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_109])).

tff(c_168,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_113])).

tff(c_171,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_168])).

tff(c_175,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_171])).

tff(c_177,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_113])).

tff(c_100,plain,(
    ! [C_72,A_73,D_74,B_75] :
      ( C_72 = A_73
      | g1_pre_topc(C_72,D_74) != g1_pre_topc(A_73,B_75)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(k1_zfmisc_1(A_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_104,plain,(
    ! [C_72,D_74] :
      ( u1_struct_0('#skF_2') = C_72
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(C_72,D_74)
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_100])).

tff(c_178,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_104])).

tff(c_198,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_178])).

tff(c_199,plain,(
    ! [C_72,D_74] :
      ( u1_struct_0('#skF_2') = C_72
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(C_72,D_74) ) ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_275,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_199])).

tff(c_38,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_36,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_151,plain,(
    ! [F_92,D_94,C_90,B_91,A_93] :
      ( r1_funct_2(A_93,B_91,C_90,D_94,F_92,F_92)
      | ~ m1_subset_1(F_92,k1_zfmisc_1(k2_zfmisc_1(C_90,D_94)))
      | ~ v1_funct_2(F_92,C_90,D_94)
      | ~ m1_subset_1(F_92,k1_zfmisc_1(k2_zfmisc_1(A_93,B_91)))
      | ~ v1_funct_2(F_92,A_93,B_91)
      | ~ v1_funct_1(F_92)
      | v1_xboole_0(D_94)
      | v1_xboole_0(B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_153,plain,(
    ! [A_93,B_91] :
      ( r1_funct_2(A_93,B_91,u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_93,B_91)))
      | ~ v1_funct_2('#skF_4',A_93,B_91)
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_91) ) ),
    inference(resolution,[status(thm)],[c_34,c_151])).

tff(c_156,plain,(
    ! [A_93,B_91] :
      ( r1_funct_2(A_93,B_91,u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_93,B_91)))
      | ~ v1_funct_2('#skF_4',A_93,B_91)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_91) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_153])).

tff(c_346,plain,(
    ! [A_93,B_91] :
      ( r1_funct_2(A_93,B_91,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_93,B_91)))
      | ~ v1_funct_2('#skF_4',A_93,B_91)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_91) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_156])).

tff(c_347,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_346])).

tff(c_18,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0(u1_struct_0(A_17))
      | ~ l1_struct_0(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_350,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_347,c_18])).

tff(c_353,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_350])).

tff(c_356,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_353])).

tff(c_360,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_356])).

tff(c_362,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_346])).

tff(c_291,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_36])).

tff(c_290,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_34])).

tff(c_361,plain,(
    ! [A_93,B_91] :
      ( r1_funct_2(A_93,B_91,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_93,B_91)))
      | ~ v1_funct_2('#skF_4',A_93,B_91)
      | v1_xboole_0(B_91) ) ),
    inference(splitRight,[status(thm)],[c_346])).

tff(c_40,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_52,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_114,plain,(
    ! [A_80,B_81,C_82,D_83] :
      ( k2_partfun1(A_80,B_81,C_82,D_83) = k7_relat_1(C_82,D_83)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81)))
      | ~ v1_funct_1(C_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_116,plain,(
    ! [D_83] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_83) = k7_relat_1('#skF_4',D_83)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_114])).

tff(c_119,plain,(
    ! [D_83] : k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_83) = k7_relat_1('#skF_4',D_83) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_116])).

tff(c_286,plain,(
    ! [D_83] : k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',D_83) = k7_relat_1('#skF_4',D_83) ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_119])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_46,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_316,plain,(
    ! [A_106,B_107,C_108,D_109] :
      ( k2_partfun1(u1_struct_0(A_106),u1_struct_0(B_107),C_108,u1_struct_0(D_109)) = k2_tmap_1(A_106,B_107,C_108,D_109)
      | ~ m1_pre_topc(D_109,A_106)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_106),u1_struct_0(B_107))))
      | ~ v1_funct_2(C_108,u1_struct_0(A_106),u1_struct_0(B_107))
      | ~ v1_funct_1(C_108)
      | ~ l1_pre_topc(B_107)
      | ~ v2_pre_topc(B_107)
      | v2_struct_0(B_107)
      | ~ l1_pre_topc(A_106)
      | ~ v2_pre_topc(A_106)
      | v2_struct_0(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_318,plain,(
    ! [B_107,C_108,D_109] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0(B_107),C_108,u1_struct_0(D_109)) = k2_tmap_1('#skF_2',B_107,C_108,D_109)
      | ~ m1_pre_topc(D_109,'#skF_2')
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_107))))
      | ~ v1_funct_2(C_108,u1_struct_0('#skF_2'),u1_struct_0(B_107))
      | ~ v1_funct_1(C_108)
      | ~ l1_pre_topc(B_107)
      | ~ v2_pre_topc(B_107)
      | v2_struct_0(B_107)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_316])).

tff(c_322,plain,(
    ! [B_107,C_108,D_109] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_107),C_108,u1_struct_0(D_109)) = k2_tmap_1('#skF_2',B_107,C_108,D_109)
      | ~ m1_pre_topc(D_109,'#skF_2')
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_107))))
      | ~ v1_funct_2(C_108,u1_struct_0('#skF_3'),u1_struct_0(B_107))
      | ~ v1_funct_1(C_108)
      | ~ l1_pre_topc(B_107)
      | ~ v2_pre_topc(B_107)
      | v2_struct_0(B_107)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_275,c_275,c_318])).

tff(c_436,plain,(
    ! [B_122,C_123,D_124] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_122),C_123,u1_struct_0(D_124)) = k2_tmap_1('#skF_2',B_122,C_123,D_124)
      | ~ m1_pre_topc(D_124,'#skF_2')
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_122))))
      | ~ v1_funct_2(C_123,u1_struct_0('#skF_3'),u1_struct_0(B_122))
      | ~ v1_funct_1(C_123)
      | ~ l1_pre_topc(B_122)
      | ~ v2_pre_topc(B_122)
      | v2_struct_0(B_122) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_322])).

tff(c_438,plain,(
    ! [D_124] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_124)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_124)
      | ~ m1_pre_topc(D_124,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_290,c_436])).

tff(c_443,plain,(
    ! [D_124] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_124)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_124)
      | ~ m1_pre_topc(D_124,'#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_38,c_291,c_286,c_438])).

tff(c_448,plain,(
    ! [D_125] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_125)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_125)
      | ~ m1_pre_topc(D_125,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_443])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_61,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_34,c_2])).

tff(c_64,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_61])).

tff(c_71,plain,(
    ! [C_65,A_66,B_67] :
      ( v4_relat_1(C_65,A_66)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_75,plain,(
    v4_relat_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_71])).

tff(c_6,plain,(
    ! [B_7,A_6] :
      ( k7_relat_1(B_7,A_6) = B_7
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_82,plain,
    ( k7_relat_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_75,c_6])).

tff(c_85,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_82])).

tff(c_288,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_85])).

tff(c_454,plain,
    ( k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4'
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_448,c_288])).

tff(c_466,plain,(
    k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_454])).

tff(c_30,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_287,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_30])).

tff(c_471,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_466,c_287])).

tff(c_480,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_361,c_471])).

tff(c_483,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_290,c_480])).

tff(c_485,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_362,c_483])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:46:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.54/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.45  
% 2.98/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.45  %$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.98/1.45  
% 2.98/1.45  %Foreground sorts:
% 2.98/1.45  
% 2.98/1.45  
% 2.98/1.45  %Background operators:
% 2.98/1.45  
% 2.98/1.45  
% 2.98/1.45  %Foreground operators:
% 2.98/1.45  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.98/1.45  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.98/1.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.98/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.98/1.45  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 2.98/1.45  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.98/1.45  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.98/1.45  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.98/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.98/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.98/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.98/1.45  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.98/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.98/1.45  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.98/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.98/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.98/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.98/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.98/1.45  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 2.98/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.98/1.45  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.98/1.45  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.98/1.45  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.98/1.45  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.98/1.45  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 2.98/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.98/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.98/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.98/1.45  
% 2.98/1.47  tff(f_159, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => r1_funct_2(u1_struct_0(B), u1_struct_0(A), u1_struct_0(C), u1_struct_0(A), D, k2_tmap_1(B, A, D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_tmap_1)).
% 2.98/1.47  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.98/1.47  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 2.98/1.47  tff(f_77, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 2.98/1.47  tff(f_99, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (r1_funct_2(A, B, C, D, E, F) <=> (E = F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 2.98/1.47  tff(f_68, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.98/1.47  tff(f_52, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.98/1.47  tff(f_126, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 2.98/1.47  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.98/1.47  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.98/1.47  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.98/1.47  tff(f_40, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.98/1.47  tff(c_50, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.98/1.47  tff(c_14, plain, (![A_15]: (l1_struct_0(A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.98/1.47  tff(c_54, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.98/1.47  tff(c_44, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.98/1.47  tff(c_16, plain, (![A_16]: (m1_subset_1(u1_pre_topc(A_16), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_16)))) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.98/1.47  tff(c_32, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.98/1.47  tff(c_109, plain, (![D_76, B_77, C_78, A_79]: (D_76=B_77 | g1_pre_topc(C_78, D_76)!=g1_pre_topc(A_79, B_77) | ~m1_subset_1(B_77, k1_zfmisc_1(k1_zfmisc_1(A_79))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.98/1.47  tff(c_113, plain, (![D_76, C_78]: (u1_pre_topc('#skF_2')=D_76 | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=g1_pre_topc(C_78, D_76) | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))))), inference(superposition, [status(thm), theory('equality')], [c_32, c_109])).
% 2.98/1.47  tff(c_168, plain, (~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_113])).
% 2.98/1.47  tff(c_171, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_16, c_168])).
% 2.98/1.47  tff(c_175, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_171])).
% 2.98/1.47  tff(c_177, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_113])).
% 2.98/1.47  tff(c_100, plain, (![C_72, A_73, D_74, B_75]: (C_72=A_73 | g1_pre_topc(C_72, D_74)!=g1_pre_topc(A_73, B_75) | ~m1_subset_1(B_75, k1_zfmisc_1(k1_zfmisc_1(A_73))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.98/1.47  tff(c_104, plain, (![C_72, D_74]: (u1_struct_0('#skF_2')=C_72 | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=g1_pre_topc(C_72, D_74) | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))))), inference(superposition, [status(thm), theory('equality')], [c_32, c_100])).
% 2.98/1.47  tff(c_178, plain, (~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_104])).
% 2.98/1.47  tff(c_198, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_177, c_178])).
% 2.98/1.47  tff(c_199, plain, (![C_72, D_74]: (u1_struct_0('#skF_2')=C_72 | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=g1_pre_topc(C_72, D_74))), inference(splitRight, [status(thm)], [c_104])).
% 2.98/1.47  tff(c_275, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_199])).
% 2.98/1.47  tff(c_38, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.98/1.47  tff(c_36, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.98/1.47  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.98/1.47  tff(c_151, plain, (![F_92, D_94, C_90, B_91, A_93]: (r1_funct_2(A_93, B_91, C_90, D_94, F_92, F_92) | ~m1_subset_1(F_92, k1_zfmisc_1(k2_zfmisc_1(C_90, D_94))) | ~v1_funct_2(F_92, C_90, D_94) | ~m1_subset_1(F_92, k1_zfmisc_1(k2_zfmisc_1(A_93, B_91))) | ~v1_funct_2(F_92, A_93, B_91) | ~v1_funct_1(F_92) | v1_xboole_0(D_94) | v1_xboole_0(B_91))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.98/1.47  tff(c_153, plain, (![A_93, B_91]: (r1_funct_2(A_93, B_91, u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_93, B_91))) | ~v1_funct_2('#skF_4', A_93, B_91) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_91))), inference(resolution, [status(thm)], [c_34, c_151])).
% 2.98/1.47  tff(c_156, plain, (![A_93, B_91]: (r1_funct_2(A_93, B_91, u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_93, B_91))) | ~v1_funct_2('#skF_4', A_93, B_91) | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_91))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_153])).
% 2.98/1.47  tff(c_346, plain, (![A_93, B_91]: (r1_funct_2(A_93, B_91, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_93, B_91))) | ~v1_funct_2('#skF_4', A_93, B_91) | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_91))), inference(demodulation, [status(thm), theory('equality')], [c_275, c_156])).
% 2.98/1.47  tff(c_347, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_346])).
% 2.98/1.47  tff(c_18, plain, (![A_17]: (~v1_xboole_0(u1_struct_0(A_17)) | ~l1_struct_0(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.98/1.47  tff(c_350, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_347, c_18])).
% 2.98/1.47  tff(c_353, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_54, c_350])).
% 2.98/1.47  tff(c_356, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_353])).
% 2.98/1.47  tff(c_360, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_356])).
% 2.98/1.47  tff(c_362, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_346])).
% 2.98/1.47  tff(c_291, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_275, c_36])).
% 2.98/1.47  tff(c_290, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_275, c_34])).
% 2.98/1.47  tff(c_361, plain, (![A_93, B_91]: (r1_funct_2(A_93, B_91, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_93, B_91))) | ~v1_funct_2('#skF_4', A_93, B_91) | v1_xboole_0(B_91))), inference(splitRight, [status(thm)], [c_346])).
% 2.98/1.47  tff(c_40, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.98/1.47  tff(c_52, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.98/1.47  tff(c_114, plain, (![A_80, B_81, C_82, D_83]: (k2_partfun1(A_80, B_81, C_82, D_83)=k7_relat_1(C_82, D_83) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))) | ~v1_funct_1(C_82))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.98/1.47  tff(c_116, plain, (![D_83]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_83)=k7_relat_1('#skF_4', D_83) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_34, c_114])).
% 2.98/1.47  tff(c_119, plain, (![D_83]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_83)=k7_relat_1('#skF_4', D_83))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_116])).
% 2.98/1.47  tff(c_286, plain, (![D_83]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', D_83)=k7_relat_1('#skF_4', D_83))), inference(demodulation, [status(thm), theory('equality')], [c_275, c_119])).
% 2.98/1.47  tff(c_48, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.98/1.47  tff(c_46, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.98/1.47  tff(c_316, plain, (![A_106, B_107, C_108, D_109]: (k2_partfun1(u1_struct_0(A_106), u1_struct_0(B_107), C_108, u1_struct_0(D_109))=k2_tmap_1(A_106, B_107, C_108, D_109) | ~m1_pre_topc(D_109, A_106) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_106), u1_struct_0(B_107)))) | ~v1_funct_2(C_108, u1_struct_0(A_106), u1_struct_0(B_107)) | ~v1_funct_1(C_108) | ~l1_pre_topc(B_107) | ~v2_pre_topc(B_107) | v2_struct_0(B_107) | ~l1_pre_topc(A_106) | ~v2_pre_topc(A_106) | v2_struct_0(A_106))), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.98/1.47  tff(c_318, plain, (![B_107, C_108, D_109]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0(B_107), C_108, u1_struct_0(D_109))=k2_tmap_1('#skF_2', B_107, C_108, D_109) | ~m1_pre_topc(D_109, '#skF_2') | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_107)))) | ~v1_funct_2(C_108, u1_struct_0('#skF_2'), u1_struct_0(B_107)) | ~v1_funct_1(C_108) | ~l1_pre_topc(B_107) | ~v2_pre_topc(B_107) | v2_struct_0(B_107) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_275, c_316])).
% 2.98/1.47  tff(c_322, plain, (![B_107, C_108, D_109]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_107), C_108, u1_struct_0(D_109))=k2_tmap_1('#skF_2', B_107, C_108, D_109) | ~m1_pre_topc(D_109, '#skF_2') | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_107)))) | ~v1_funct_2(C_108, u1_struct_0('#skF_3'), u1_struct_0(B_107)) | ~v1_funct_1(C_108) | ~l1_pre_topc(B_107) | ~v2_pre_topc(B_107) | v2_struct_0(B_107) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_275, c_275, c_318])).
% 2.98/1.47  tff(c_436, plain, (![B_122, C_123, D_124]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_122), C_123, u1_struct_0(D_124))=k2_tmap_1('#skF_2', B_122, C_123, D_124) | ~m1_pre_topc(D_124, '#skF_2') | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_122)))) | ~v1_funct_2(C_123, u1_struct_0('#skF_3'), u1_struct_0(B_122)) | ~v1_funct_1(C_123) | ~l1_pre_topc(B_122) | ~v2_pre_topc(B_122) | v2_struct_0(B_122))), inference(negUnitSimplification, [status(thm)], [c_48, c_322])).
% 2.98/1.47  tff(c_438, plain, (![D_124]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_124))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_124) | ~m1_pre_topc(D_124, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_290, c_436])).
% 2.98/1.47  tff(c_443, plain, (![D_124]: (k7_relat_1('#skF_4', u1_struct_0(D_124))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_124) | ~m1_pre_topc(D_124, '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_38, c_291, c_286, c_438])).
% 2.98/1.47  tff(c_448, plain, (![D_125]: (k7_relat_1('#skF_4', u1_struct_0(D_125))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_125) | ~m1_pre_topc(D_125, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_54, c_443])).
% 2.98/1.47  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.98/1.47  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.98/1.47  tff(c_61, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_34, c_2])).
% 2.98/1.47  tff(c_64, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_61])).
% 2.98/1.47  tff(c_71, plain, (![C_65, A_66, B_67]: (v4_relat_1(C_65, A_66) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.98/1.47  tff(c_75, plain, (v4_relat_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_34, c_71])).
% 2.98/1.47  tff(c_6, plain, (![B_7, A_6]: (k7_relat_1(B_7, A_6)=B_7 | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.98/1.47  tff(c_82, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_2'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_75, c_6])).
% 2.98/1.47  tff(c_85, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_2'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_82])).
% 2.98/1.47  tff(c_288, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_275, c_85])).
% 2.98/1.47  tff(c_454, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4' | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_448, c_288])).
% 2.98/1.47  tff(c_466, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_454])).
% 2.98/1.47  tff(c_30, plain, (~r1_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.98/1.47  tff(c_287, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_275, c_30])).
% 2.98/1.47  tff(c_471, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_466, c_287])).
% 2.98/1.47  tff(c_480, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_361, c_471])).
% 2.98/1.47  tff(c_483, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_291, c_290, c_480])).
% 2.98/1.47  tff(c_485, plain, $false, inference(negUnitSimplification, [status(thm)], [c_362, c_483])).
% 2.98/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.47  
% 2.98/1.47  Inference rules
% 2.98/1.47  ----------------------
% 2.98/1.47  #Ref     : 8
% 2.98/1.47  #Sup     : 76
% 2.98/1.47  #Fact    : 0
% 2.98/1.47  #Define  : 0
% 2.98/1.47  #Split   : 7
% 2.98/1.47  #Chain   : 0
% 2.98/1.47  #Close   : 0
% 2.98/1.47  
% 2.98/1.47  Ordering : KBO
% 2.98/1.47  
% 2.98/1.47  Simplification rules
% 2.98/1.47  ----------------------
% 2.98/1.47  #Subsume      : 15
% 2.98/1.47  #Demod        : 89
% 2.98/1.47  #Tautology    : 45
% 2.98/1.47  #SimpNegUnit  : 11
% 2.98/1.47  #BackRed      : 13
% 2.98/1.47  
% 2.98/1.47  #Partial instantiations: 0
% 2.98/1.47  #Strategies tried      : 1
% 2.98/1.47  
% 2.98/1.47  Timing (in seconds)
% 2.98/1.47  ----------------------
% 2.98/1.48  Preprocessing        : 0.35
% 2.98/1.48  Parsing              : 0.19
% 2.98/1.48  CNF conversion       : 0.03
% 2.98/1.48  Main loop            : 0.29
% 2.98/1.48  Inferencing          : 0.10
% 2.98/1.48  Reduction            : 0.09
% 2.98/1.48  Demodulation         : 0.06
% 2.98/1.48  BG Simplification    : 0.02
% 2.98/1.48  Subsumption          : 0.05
% 2.98/1.48  Abstraction          : 0.01
% 2.98/1.48  MUC search           : 0.00
% 2.98/1.48  Cooper               : 0.00
% 2.98/1.48  Total                : 0.68
% 2.98/1.48  Index Insertion      : 0.00
% 2.98/1.48  Index Deletion       : 0.00
% 2.98/1.48  Index Matching       : 0.00
% 2.98/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
