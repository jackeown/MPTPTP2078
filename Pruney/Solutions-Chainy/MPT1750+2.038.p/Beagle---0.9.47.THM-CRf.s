%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:56 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 205 expanded)
%              Number of leaves         :   40 (  86 expanded)
%              Depth                    :   11
%              Number of atoms          :  192 ( 863 expanded)
%              Number of equality atoms :   28 ( 139 expanded)
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

tff(f_157,negated_conjecture,(
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

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_77,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_97,axiom,(
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

tff(f_68,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_124,axiom,(
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

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(c_48,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_14,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_42,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_16,plain,(
    ! [A_16] :
      ( m1_subset_1(u1_pre_topc(A_16),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_16))))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_30,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_98,plain,(
    ! [C_72,A_73,D_74,B_75] :
      ( C_72 = A_73
      | g1_pre_topc(C_72,D_74) != g1_pre_topc(A_73,B_75)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(k1_zfmisc_1(A_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_102,plain,(
    ! [C_72,D_74] :
      ( u1_struct_0('#skF_2') = C_72
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(C_72,D_74)
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_98])).

tff(c_166,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_102])).

tff(c_169,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_166])).

tff(c_173,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_169])).

tff(c_174,plain,(
    ! [C_72,D_74] :
      ( u1_struct_0('#skF_2') = C_72
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(C_72,D_74) ) ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_228,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_174])).

tff(c_36,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_34,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_149,plain,(
    ! [D_95,C_90,B_91,E_92,F_93,A_94] :
      ( r1_funct_2(A_94,B_91,C_90,D_95,E_92,E_92)
      | ~ m1_subset_1(F_93,k1_zfmisc_1(k2_zfmisc_1(C_90,D_95)))
      | ~ v1_funct_2(F_93,C_90,D_95)
      | ~ v1_funct_1(F_93)
      | ~ m1_subset_1(E_92,k1_zfmisc_1(k2_zfmisc_1(A_94,B_91)))
      | ~ v1_funct_2(E_92,A_94,B_91)
      | ~ v1_funct_1(E_92)
      | v1_xboole_0(D_95)
      | v1_xboole_0(B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_151,plain,(
    ! [A_94,B_91,E_92] :
      ( r1_funct_2(A_94,B_91,u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),E_92,E_92)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_92,k1_zfmisc_1(k2_zfmisc_1(A_94,B_91)))
      | ~ v1_funct_2(E_92,A_94,B_91)
      | ~ v1_funct_1(E_92)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_91) ) ),
    inference(resolution,[status(thm)],[c_32,c_149])).

tff(c_154,plain,(
    ! [A_94,B_91,E_92] :
      ( r1_funct_2(A_94,B_91,u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),E_92,E_92)
      | ~ m1_subset_1(E_92,k1_zfmisc_1(k2_zfmisc_1(A_94,B_91)))
      | ~ v1_funct_2(E_92,A_94,B_91)
      | ~ v1_funct_1(E_92)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_91) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_151])).

tff(c_404,plain,(
    ! [A_94,B_91,E_92] :
      ( r1_funct_2(A_94,B_91,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),E_92,E_92)
      | ~ m1_subset_1(E_92,k1_zfmisc_1(k2_zfmisc_1(A_94,B_91)))
      | ~ v1_funct_2(E_92,A_94,B_91)
      | ~ v1_funct_1(E_92)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_91) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_154])).

tff(c_405,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_404])).

tff(c_18,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0(u1_struct_0(A_17))
      | ~ l1_struct_0(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_408,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_405,c_18])).

tff(c_411,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_408])).

tff(c_414,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_411])).

tff(c_418,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_414])).

tff(c_420,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_404])).

tff(c_244,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_34])).

tff(c_243,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_32])).

tff(c_422,plain,(
    ! [A_111,B_112,E_113] :
      ( r1_funct_2(A_111,B_112,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),E_113,E_113)
      | ~ m1_subset_1(E_113,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112)))
      | ~ v1_funct_2(E_113,A_111,B_112)
      | ~ v1_funct_1(E_113)
      | v1_xboole_0(B_112) ) ),
    inference(splitRight,[status(thm)],[c_404])).

tff(c_38,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_44,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_50,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_112,plain,(
    ! [A_80,B_81,C_82,D_83] :
      ( k2_partfun1(A_80,B_81,C_82,D_83) = k7_relat_1(C_82,D_83)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81)))
      | ~ v1_funct_1(C_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_114,plain,(
    ! [D_83] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_83) = k7_relat_1('#skF_4',D_83)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_32,c_112])).

tff(c_117,plain,(
    ! [D_83] : k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_83) = k7_relat_1('#skF_4',D_83) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_114])).

tff(c_219,plain,(
    ! [A_97,B_98,C_99,D_100] :
      ( k2_partfun1(u1_struct_0(A_97),u1_struct_0(B_98),C_99,u1_struct_0(D_100)) = k2_tmap_1(A_97,B_98,C_99,D_100)
      | ~ m1_pre_topc(D_100,A_97)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_97),u1_struct_0(B_98))))
      | ~ v1_funct_2(C_99,u1_struct_0(A_97),u1_struct_0(B_98))
      | ~ v1_funct_1(C_99)
      | ~ l1_pre_topc(B_98)
      | ~ v2_pre_topc(B_98)
      | v2_struct_0(B_98)
      | ~ l1_pre_topc(A_97)
      | ~ v2_pre_topc(A_97)
      | v2_struct_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_221,plain,(
    ! [D_100] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_100)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_100)
      | ~ m1_pre_topc(D_100,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_32,c_219])).

tff(c_224,plain,(
    ! [D_100] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_100)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_100)
      | ~ m1_pre_topc(D_100,'#skF_2')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_50,c_48,c_36,c_34,c_117,c_221])).

tff(c_354,plain,(
    ! [D_105] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_105)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_105)
      | ~ m1_pre_topc(D_105,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_52,c_224])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_56,plain,(
    ! [B_60,A_61] :
      ( v1_relat_1(B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_61))
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_59,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_32,c_56])).

tff(c_62,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_59])).

tff(c_77,plain,(
    ! [C_66,A_67,B_68] :
      ( v4_relat_1(C_66,A_67)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_81,plain,(
    v4_relat_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_77])).

tff(c_82,plain,(
    ! [B_69,A_70] :
      ( k7_relat_1(B_69,A_70) = B_69
      | ~ v4_relat_1(B_69,A_70)
      | ~ v1_relat_1(B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_85,plain,
    ( k7_relat_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_81,c_82])).

tff(c_88,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_85])).

tff(c_240,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_88])).

tff(c_360,plain,
    ( k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4'
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_354,c_240])).

tff(c_372,plain,(
    k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_360])).

tff(c_28,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_239,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_28])).

tff(c_421,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_372,c_239])).

tff(c_425,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_422,c_421])).

tff(c_428,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_244,c_243,c_425])).

tff(c_430,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_420,c_428])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:05:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.50/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.44  
% 2.79/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.44  %$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.79/1.44  
% 2.79/1.44  %Foreground sorts:
% 2.79/1.44  
% 2.79/1.44  
% 2.79/1.44  %Background operators:
% 2.79/1.44  
% 2.79/1.44  
% 2.79/1.44  %Foreground operators:
% 2.79/1.44  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.79/1.44  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.79/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.79/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.79/1.44  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 2.79/1.44  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.79/1.44  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.79/1.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.79/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.79/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.79/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.79/1.44  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.79/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.79/1.44  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.79/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.79/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.79/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.79/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.79/1.44  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 2.79/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.79/1.44  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.79/1.44  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.79/1.44  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.79/1.44  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.79/1.44  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 2.79/1.44  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.79/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.79/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.79/1.44  
% 2.79/1.46  tff(f_157, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => r1_funct_2(u1_struct_0(B), u1_struct_0(A), u1_struct_0(C), u1_struct_0(A), D, k2_tmap_1(B, A, D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_tmap_1)).
% 2.79/1.46  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.79/1.46  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 2.79/1.46  tff(f_77, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 2.79/1.46  tff(f_97, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => r1_funct_2(A, B, C, D, E, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r1_funct_2)).
% 2.79/1.46  tff(f_68, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.79/1.46  tff(f_52, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.79/1.46  tff(f_124, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 2.79/1.46  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.79/1.46  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.79/1.46  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.79/1.46  tff(f_40, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.79/1.46  tff(c_48, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.79/1.46  tff(c_14, plain, (![A_15]: (l1_struct_0(A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.79/1.46  tff(c_52, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.79/1.46  tff(c_42, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.79/1.46  tff(c_16, plain, (![A_16]: (m1_subset_1(u1_pre_topc(A_16), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_16)))) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.79/1.46  tff(c_30, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.79/1.46  tff(c_98, plain, (![C_72, A_73, D_74, B_75]: (C_72=A_73 | g1_pre_topc(C_72, D_74)!=g1_pre_topc(A_73, B_75) | ~m1_subset_1(B_75, k1_zfmisc_1(k1_zfmisc_1(A_73))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.79/1.46  tff(c_102, plain, (![C_72, D_74]: (u1_struct_0('#skF_2')=C_72 | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=g1_pre_topc(C_72, D_74) | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))))), inference(superposition, [status(thm), theory('equality')], [c_30, c_98])).
% 2.79/1.46  tff(c_166, plain, (~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_102])).
% 2.79/1.46  tff(c_169, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_16, c_166])).
% 2.79/1.46  tff(c_173, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_169])).
% 2.79/1.46  tff(c_174, plain, (![C_72, D_74]: (u1_struct_0('#skF_2')=C_72 | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=g1_pre_topc(C_72, D_74))), inference(splitRight, [status(thm)], [c_102])).
% 2.79/1.46  tff(c_228, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_174])).
% 2.79/1.46  tff(c_36, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.79/1.46  tff(c_34, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.79/1.46  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.79/1.46  tff(c_149, plain, (![D_95, C_90, B_91, E_92, F_93, A_94]: (r1_funct_2(A_94, B_91, C_90, D_95, E_92, E_92) | ~m1_subset_1(F_93, k1_zfmisc_1(k2_zfmisc_1(C_90, D_95))) | ~v1_funct_2(F_93, C_90, D_95) | ~v1_funct_1(F_93) | ~m1_subset_1(E_92, k1_zfmisc_1(k2_zfmisc_1(A_94, B_91))) | ~v1_funct_2(E_92, A_94, B_91) | ~v1_funct_1(E_92) | v1_xboole_0(D_95) | v1_xboole_0(B_91))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.79/1.46  tff(c_151, plain, (![A_94, B_91, E_92]: (r1_funct_2(A_94, B_91, u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), E_92, E_92) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_92, k1_zfmisc_1(k2_zfmisc_1(A_94, B_91))) | ~v1_funct_2(E_92, A_94, B_91) | ~v1_funct_1(E_92) | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_91))), inference(resolution, [status(thm)], [c_32, c_149])).
% 2.79/1.46  tff(c_154, plain, (![A_94, B_91, E_92]: (r1_funct_2(A_94, B_91, u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), E_92, E_92) | ~m1_subset_1(E_92, k1_zfmisc_1(k2_zfmisc_1(A_94, B_91))) | ~v1_funct_2(E_92, A_94, B_91) | ~v1_funct_1(E_92) | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_91))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_151])).
% 2.79/1.46  tff(c_404, plain, (![A_94, B_91, E_92]: (r1_funct_2(A_94, B_91, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), E_92, E_92) | ~m1_subset_1(E_92, k1_zfmisc_1(k2_zfmisc_1(A_94, B_91))) | ~v1_funct_2(E_92, A_94, B_91) | ~v1_funct_1(E_92) | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_91))), inference(demodulation, [status(thm), theory('equality')], [c_228, c_154])).
% 2.79/1.46  tff(c_405, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_404])).
% 2.79/1.46  tff(c_18, plain, (![A_17]: (~v1_xboole_0(u1_struct_0(A_17)) | ~l1_struct_0(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.79/1.46  tff(c_408, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_405, c_18])).
% 2.79/1.46  tff(c_411, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_52, c_408])).
% 2.79/1.46  tff(c_414, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_411])).
% 2.79/1.46  tff(c_418, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_414])).
% 2.79/1.46  tff(c_420, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_404])).
% 2.79/1.46  tff(c_244, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_228, c_34])).
% 2.79/1.46  tff(c_243, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_228, c_32])).
% 2.79/1.46  tff(c_422, plain, (![A_111, B_112, E_113]: (r1_funct_2(A_111, B_112, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), E_113, E_113) | ~m1_subset_1(E_113, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))) | ~v1_funct_2(E_113, A_111, B_112) | ~v1_funct_1(E_113) | v1_xboole_0(B_112))), inference(splitRight, [status(thm)], [c_404])).
% 2.79/1.46  tff(c_38, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.79/1.46  tff(c_46, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.79/1.46  tff(c_44, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.79/1.46  tff(c_50, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.79/1.46  tff(c_112, plain, (![A_80, B_81, C_82, D_83]: (k2_partfun1(A_80, B_81, C_82, D_83)=k7_relat_1(C_82, D_83) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))) | ~v1_funct_1(C_82))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.79/1.46  tff(c_114, plain, (![D_83]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_83)=k7_relat_1('#skF_4', D_83) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_32, c_112])).
% 2.79/1.46  tff(c_117, plain, (![D_83]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_83)=k7_relat_1('#skF_4', D_83))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_114])).
% 2.79/1.46  tff(c_219, plain, (![A_97, B_98, C_99, D_100]: (k2_partfun1(u1_struct_0(A_97), u1_struct_0(B_98), C_99, u1_struct_0(D_100))=k2_tmap_1(A_97, B_98, C_99, D_100) | ~m1_pre_topc(D_100, A_97) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_97), u1_struct_0(B_98)))) | ~v1_funct_2(C_99, u1_struct_0(A_97), u1_struct_0(B_98)) | ~v1_funct_1(C_99) | ~l1_pre_topc(B_98) | ~v2_pre_topc(B_98) | v2_struct_0(B_98) | ~l1_pre_topc(A_97) | ~v2_pre_topc(A_97) | v2_struct_0(A_97))), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.79/1.46  tff(c_221, plain, (![D_100]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_100))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_100) | ~m1_pre_topc(D_100, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_219])).
% 2.79/1.46  tff(c_224, plain, (![D_100]: (k7_relat_1('#skF_4', u1_struct_0(D_100))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_100) | ~m1_pre_topc(D_100, '#skF_2') | v2_struct_0('#skF_1') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_50, c_48, c_36, c_34, c_117, c_221])).
% 2.79/1.46  tff(c_354, plain, (![D_105]: (k7_relat_1('#skF_4', u1_struct_0(D_105))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_105) | ~m1_pre_topc(D_105, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_46, c_52, c_224])).
% 2.79/1.46  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.79/1.46  tff(c_56, plain, (![B_60, A_61]: (v1_relat_1(B_60) | ~m1_subset_1(B_60, k1_zfmisc_1(A_61)) | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.79/1.46  tff(c_59, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_32, c_56])).
% 2.79/1.46  tff(c_62, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_59])).
% 2.79/1.46  tff(c_77, plain, (![C_66, A_67, B_68]: (v4_relat_1(C_66, A_67) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.79/1.46  tff(c_81, plain, (v4_relat_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_77])).
% 2.79/1.46  tff(c_82, plain, (![B_69, A_70]: (k7_relat_1(B_69, A_70)=B_69 | ~v4_relat_1(B_69, A_70) | ~v1_relat_1(B_69))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.79/1.46  tff(c_85, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_2'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_81, c_82])).
% 2.79/1.46  tff(c_88, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_2'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_85])).
% 2.79/1.46  tff(c_240, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_228, c_88])).
% 2.79/1.46  tff(c_360, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4' | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_354, c_240])).
% 2.79/1.46  tff(c_372, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_360])).
% 2.79/1.46  tff(c_28, plain, (~r1_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.79/1.46  tff(c_239, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_228, c_28])).
% 2.79/1.46  tff(c_421, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_372, c_239])).
% 2.79/1.46  tff(c_425, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_422, c_421])).
% 2.79/1.46  tff(c_428, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_244, c_243, c_425])).
% 2.79/1.46  tff(c_430, plain, $false, inference(negUnitSimplification, [status(thm)], [c_420, c_428])).
% 2.79/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.46  
% 2.79/1.46  Inference rules
% 2.79/1.46  ----------------------
% 2.79/1.46  #Ref     : 8
% 2.79/1.46  #Sup     : 64
% 2.79/1.46  #Fact    : 0
% 2.79/1.46  #Define  : 0
% 2.79/1.46  #Split   : 7
% 2.79/1.46  #Chain   : 0
% 2.79/1.46  #Close   : 0
% 2.79/1.46  
% 2.79/1.46  Ordering : KBO
% 2.79/1.46  
% 2.79/1.46  Simplification rules
% 2.79/1.46  ----------------------
% 2.79/1.46  #Subsume      : 8
% 2.79/1.46  #Demod        : 76
% 2.79/1.46  #Tautology    : 40
% 2.79/1.46  #SimpNegUnit  : 7
% 2.79/1.46  #BackRed      : 11
% 2.79/1.46  
% 2.79/1.46  #Partial instantiations: 0
% 2.79/1.46  #Strategies tried      : 1
% 2.79/1.46  
% 2.79/1.46  Timing (in seconds)
% 2.79/1.46  ----------------------
% 2.91/1.46  Preprocessing        : 0.35
% 2.91/1.46  Parsing              : 0.20
% 2.91/1.46  CNF conversion       : 0.02
% 2.91/1.46  Main loop            : 0.26
% 2.91/1.46  Inferencing          : 0.10
% 2.91/1.46  Reduction            : 0.08
% 2.91/1.46  Demodulation         : 0.06
% 2.91/1.46  BG Simplification    : 0.02
% 2.91/1.46  Subsumption          : 0.05
% 2.91/1.46  Abstraction          : 0.01
% 2.91/1.46  MUC search           : 0.00
% 2.91/1.46  Cooper               : 0.00
% 2.91/1.46  Total                : 0.65
% 2.91/1.46  Index Insertion      : 0.00
% 2.91/1.46  Index Deletion       : 0.00
% 2.91/1.46  Index Matching       : 0.00
% 2.91/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
