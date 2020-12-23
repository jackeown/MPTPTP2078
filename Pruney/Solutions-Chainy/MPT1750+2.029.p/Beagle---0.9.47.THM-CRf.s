%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:55 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :  137 (2457 expanded)
%              Number of leaves         :   47 ( 945 expanded)
%              Depth                    :   19
%              Number of atoms          :  313 (13302 expanded)
%              Number of equality atoms :   43 (1470 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k1_tsep_1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_tsep_1,type,(
    k1_tsep_1: ( $i * $i * $i ) > $i )).

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

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_216,negated_conjecture,(
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

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

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
     => r1_funct_2(A,B,C,D,E,E) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r1_funct_2)).

tff(f_61,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_179,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => k1_tsep_1(A,B,B) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tmap_1)).

tff(f_164,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

tff(f_79,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_pre_topc)).

tff(f_183,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_49,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_155,axiom,(
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

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_128,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & v1_pre_topc(D)
                    & m1_pre_topc(D,A) )
                 => ( D = k1_tsep_1(A,B,C)
                  <=> u1_struct_0(D) = k2_xboole_0(u1_struct_0(B),u1_struct_0(C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tsep_1)).

tff(c_62,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_14,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_50,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_48,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_315,plain,(
    ! [E_115,C_114,A_117,F_118,D_119,B_116] :
      ( r1_funct_2(A_117,B_116,C_114,D_119,E_115,E_115)
      | ~ m1_subset_1(F_118,k1_zfmisc_1(k2_zfmisc_1(C_114,D_119)))
      | ~ v1_funct_2(F_118,C_114,D_119)
      | ~ v1_funct_1(F_118)
      | ~ m1_subset_1(E_115,k1_zfmisc_1(k2_zfmisc_1(A_117,B_116)))
      | ~ v1_funct_2(E_115,A_117,B_116)
      | ~ v1_funct_1(E_115)
      | v1_xboole_0(D_119)
      | v1_xboole_0(B_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_317,plain,(
    ! [A_117,B_116,E_115] :
      ( r1_funct_2(A_117,B_116,u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),E_115,E_115)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_115,k1_zfmisc_1(k2_zfmisc_1(A_117,B_116)))
      | ~ v1_funct_2(E_115,A_117,B_116)
      | ~ v1_funct_1(E_115)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_116) ) ),
    inference(resolution,[status(thm)],[c_46,c_315])).

tff(c_320,plain,(
    ! [A_117,B_116,E_115] :
      ( r1_funct_2(A_117,B_116,u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),E_115,E_115)
      | ~ m1_subset_1(E_115,k1_zfmisc_1(k2_zfmisc_1(A_117,B_116)))
      | ~ v1_funct_2(E_115,A_117,B_116)
      | ~ v1_funct_1(E_115)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_317])).

tff(c_323,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_320])).

tff(c_16,plain,(
    ! [A_16] :
      ( ~ v1_xboole_0(u1_struct_0(A_16))
      | ~ l1_struct_0(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_326,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_323,c_16])).

tff(c_329,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_326])).

tff(c_332,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_329])).

tff(c_336,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_332])).

tff(c_338,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_320])).

tff(c_56,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_52,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_58,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_203,plain,(
    ! [A_106,B_107] :
      ( k1_tsep_1(A_106,B_107,B_107) = g1_pre_topc(u1_struct_0(B_107),u1_pre_topc(B_107))
      | ~ m1_pre_topc(B_107,A_106)
      | v2_struct_0(B_107)
      | ~ l1_pre_topc(A_106)
      | ~ v2_pre_topc(A_106)
      | v2_struct_0(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_211,plain,
    ( g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = k1_tsep_1('#skF_2','#skF_3','#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_203])).

tff(c_219,plain,
    ( g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = k1_tsep_1('#skF_2','#skF_3','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_211])).

tff(c_220,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = k1_tsep_1('#skF_2','#skF_3','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_219])).

tff(c_34,plain,(
    ! [B_57,A_55] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_57),u1_pre_topc(B_57)),A_55)
      | ~ m1_pre_topc(B_57,A_55)
      | ~ l1_pre_topc(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_236,plain,(
    ! [A_55] :
      ( m1_pre_topc(k1_tsep_1('#skF_2','#skF_3','#skF_3'),A_55)
      | ~ m1_pre_topc('#skF_3',A_55)
      | ~ l1_pre_topc(A_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_34])).

tff(c_44,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_109,plain,(
    ! [A_88] :
      ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(A_88),u1_pre_topc(A_88)))
      | ~ l1_pre_topc(A_88)
      | v2_struct_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_112,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_109])).

tff(c_114,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_112])).

tff(c_115,plain,(
    ~ v2_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_114])).

tff(c_225,plain,(
    ~ v2_struct_0(k1_tsep_1('#skF_2','#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_115])).

tff(c_40,plain,(
    ! [A_61] :
      ( m1_pre_topc(A_61,A_61)
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_64,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_157,plain,(
    ! [A_97,B_98,C_99,D_100] :
      ( k2_partfun1(A_97,B_98,C_99,D_100) = k7_relat_1(C_99,D_100)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98)))
      | ~ v1_funct_1(C_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_159,plain,(
    ! [D_100] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_100) = k7_relat_1('#skF_4',D_100)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_46,c_157])).

tff(c_162,plain,(
    ! [D_100] : k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_100) = k7_relat_1('#skF_4',D_100) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_159])).

tff(c_401,plain,(
    ! [A_123,B_124,C_125,D_126] :
      ( k2_partfun1(u1_struct_0(A_123),u1_struct_0(B_124),C_125,u1_struct_0(D_126)) = k2_tmap_1(A_123,B_124,C_125,D_126)
      | ~ m1_pre_topc(D_126,A_123)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_123),u1_struct_0(B_124))))
      | ~ v1_funct_2(C_125,u1_struct_0(A_123),u1_struct_0(B_124))
      | ~ v1_funct_1(C_125)
      | ~ l1_pre_topc(B_124)
      | ~ v2_pre_topc(B_124)
      | v2_struct_0(B_124)
      | ~ l1_pre_topc(A_123)
      | ~ v2_pre_topc(A_123)
      | v2_struct_0(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_407,plain,(
    ! [D_126] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_126)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_126)
      | ~ m1_pre_topc(D_126,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_46,c_401])).

tff(c_416,plain,(
    ! [D_126] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_126)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_126)
      | ~ m1_pre_topc(D_126,'#skF_2')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_64,c_62,c_50,c_48,c_162,c_407])).

tff(c_418,plain,(
    ! [D_127] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_127)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_127)
      | ~ m1_pre_topc(D_127,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_66,c_416])).

tff(c_79,plain,(
    ! [C_77,A_78,B_79] :
      ( v1_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_83,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_79])).

tff(c_84,plain,(
    ! [C_80,A_81,B_82] :
      ( v4_relat_1(C_80,A_81)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_88,plain,(
    v4_relat_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_46,c_84])).

tff(c_98,plain,(
    ! [B_86,A_87] :
      ( k7_relat_1(B_86,A_87) = B_86
      | ~ v4_relat_1(B_86,A_87)
      | ~ v1_relat_1(B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_101,plain,
    ( k7_relat_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_88,c_98])).

tff(c_104,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_101])).

tff(c_424,plain,
    ( k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_2') = '#skF_4'
    | ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_418,c_104])).

tff(c_436,plain,(
    ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_424])).

tff(c_439,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_436])).

tff(c_443,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_439])).

tff(c_445,plain,(
    m1_pre_topc('#skF_2','#skF_2') ),
    inference(splitRight,[status(thm)],[c_424])).

tff(c_488,plain,(
    ! [A_128] :
      ( k1_tsep_1(A_128,A_128,A_128) = g1_pre_topc(u1_struct_0(A_128),u1_pre_topc(A_128))
      | ~ v2_pre_topc(A_128)
      | v2_struct_0(A_128)
      | ~ l1_pre_topc(A_128) ) ),
    inference(resolution,[status(thm)],[c_40,c_203])).

tff(c_226,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k1_tsep_1('#skF_2','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_44])).

tff(c_499,plain,
    ( k1_tsep_1('#skF_2','#skF_2','#skF_2') = k1_tsep_1('#skF_2','#skF_3','#skF_3')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_488,c_226])).

tff(c_540,plain,
    ( k1_tsep_1('#skF_2','#skF_2','#skF_2') = k1_tsep_1('#skF_2','#skF_3','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_499])).

tff(c_541,plain,(
    k1_tsep_1('#skF_2','#skF_2','#skF_2') = k1_tsep_1('#skF_2','#skF_3','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_540])).

tff(c_116,plain,(
    ! [A_89] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_89),u1_pre_topc(A_89)))
      | ~ l1_pre_topc(A_89)
      | ~ v2_pre_topc(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_119,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_116])).

tff(c_121,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_119])).

tff(c_224,plain,(
    v1_pre_topc(k1_tsep_1('#skF_2','#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_121])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_341,plain,(
    ! [A_120,B_121,C_122] :
      ( u1_struct_0(k1_tsep_1(A_120,B_121,C_122)) = k2_xboole_0(u1_struct_0(B_121),u1_struct_0(C_122))
      | ~ m1_pre_topc(k1_tsep_1(A_120,B_121,C_122),A_120)
      | ~ v1_pre_topc(k1_tsep_1(A_120,B_121,C_122))
      | v2_struct_0(k1_tsep_1(A_120,B_121,C_122))
      | ~ m1_pre_topc(C_122,A_120)
      | v2_struct_0(C_122)
      | ~ m1_pre_topc(B_121,A_120)
      | v2_struct_0(B_121)
      | ~ l1_pre_topc(A_120)
      | v2_struct_0(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_344,plain,
    ( k2_xboole_0(u1_struct_0('#skF_3'),u1_struct_0('#skF_3')) = u1_struct_0(k1_tsep_1('#skF_2','#skF_3','#skF_3'))
    | ~ v1_pre_topc(k1_tsep_1('#skF_2','#skF_3','#skF_3'))
    | v2_struct_0(k1_tsep_1('#skF_2','#skF_3','#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_236,c_341])).

tff(c_350,plain,
    ( u1_struct_0(k1_tsep_1('#skF_2','#skF_3','#skF_3')) = u1_struct_0('#skF_3')
    | v2_struct_0(k1_tsep_1('#skF_2','#skF_3','#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_224,c_2,c_344])).

tff(c_351,plain,(
    u1_struct_0(k1_tsep_1('#skF_2','#skF_3','#skF_3')) = u1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_225,c_350])).

tff(c_30,plain,(
    ! [A_25,B_33,C_37] :
      ( u1_struct_0(k1_tsep_1(A_25,B_33,C_37)) = k2_xboole_0(u1_struct_0(B_33),u1_struct_0(C_37))
      | ~ m1_pre_topc(k1_tsep_1(A_25,B_33,C_37),A_25)
      | ~ v1_pre_topc(k1_tsep_1(A_25,B_33,C_37))
      | v2_struct_0(k1_tsep_1(A_25,B_33,C_37))
      | ~ m1_pre_topc(C_37,A_25)
      | v2_struct_0(C_37)
      | ~ m1_pre_topc(B_33,A_25)
      | v2_struct_0(B_33)
      | ~ l1_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_555,plain,
    ( k2_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_2')) = u1_struct_0(k1_tsep_1('#skF_2','#skF_2','#skF_2'))
    | ~ m1_pre_topc(k1_tsep_1('#skF_2','#skF_3','#skF_3'),'#skF_2')
    | ~ v1_pre_topc(k1_tsep_1('#skF_2','#skF_2','#skF_2'))
    | v2_struct_0(k1_tsep_1('#skF_2','#skF_2','#skF_2'))
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_541,c_30])).

tff(c_559,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ m1_pre_topc(k1_tsep_1('#skF_2','#skF_3','#skF_3'),'#skF_2')
    | v2_struct_0(k1_tsep_1('#skF_2','#skF_3','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_445,c_445,c_541,c_224,c_541,c_351,c_541,c_2,c_555])).

tff(c_560,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ m1_pre_topc(k1_tsep_1('#skF_2','#skF_3','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_225,c_559])).

tff(c_564,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_2','#skF_3','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_560])).

tff(c_567,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_236,c_564])).

tff(c_574,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_567])).

tff(c_575,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_560])).

tff(c_583,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_575,c_48])).

tff(c_582,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_575,c_46])).

tff(c_337,plain,(
    ! [A_117,B_116,E_115] :
      ( r1_funct_2(A_117,B_116,u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),E_115,E_115)
      | ~ m1_subset_1(E_115,k1_zfmisc_1(k2_zfmisc_1(A_117,B_116)))
      | ~ v1_funct_2(E_115,A_117,B_116)
      | ~ v1_funct_1(E_115)
      | v1_xboole_0(B_116) ) ),
    inference(splitRight,[status(thm)],[c_320])).

tff(c_668,plain,(
    ! [A_117,B_116,E_115] :
      ( r1_funct_2(A_117,B_116,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),E_115,E_115)
      | ~ m1_subset_1(E_115,k1_zfmisc_1(k2_zfmisc_1(A_117,B_116)))
      | ~ v1_funct_2(E_115,A_117,B_116)
      | ~ v1_funct_1(E_115)
      | v1_xboole_0(B_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_575,c_337])).

tff(c_417,plain,(
    ! [D_126] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_126)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_126)
      | ~ m1_pre_topc(D_126,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_66,c_416])).

tff(c_580,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_575,c_104])).

tff(c_661,plain,
    ( k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4'
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_417,c_580])).

tff(c_667,plain,(
    k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_661])).

tff(c_42,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_579,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_575,c_42])).

tff(c_966,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_667,c_579])).

tff(c_969,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_668,c_966])).

tff(c_972,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_583,c_582,c_969])).

tff(c_974,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_338,c_972])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:30:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.53/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.59  
% 3.53/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.59  %$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k1_tsep_1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.53/1.59  
% 3.53/1.59  %Foreground sorts:
% 3.53/1.59  
% 3.53/1.59  
% 3.53/1.59  %Background operators:
% 3.53/1.59  
% 3.53/1.59  
% 3.53/1.59  %Foreground operators:
% 3.53/1.59  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.53/1.59  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 3.53/1.59  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.53/1.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.53/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.53/1.59  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 3.53/1.59  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.53/1.59  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.53/1.59  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.53/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.53/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.53/1.59  tff('#skF_1', type, '#skF_1': $i).
% 3.53/1.59  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.53/1.59  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.53/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.53/1.59  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.53/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.53/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.53/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.53/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.53/1.59  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 3.53/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.53/1.59  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.53/1.59  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.53/1.59  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.53/1.59  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.53/1.59  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.53/1.59  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.53/1.59  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.53/1.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.53/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.53/1.59  
% 3.53/1.62  tff(f_216, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => r1_funct_2(u1_struct_0(B), u1_struct_0(A), u1_struct_0(C), u1_struct_0(A), D, k2_tmap_1(B, A, D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_tmap_1)).
% 3.53/1.62  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.53/1.62  tff(f_99, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => r1_funct_2(A, B, C, D, E, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r1_funct_2)).
% 3.53/1.62  tff(f_61, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.53/1.62  tff(f_179, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (k1_tsep_1(A, B, B) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_tmap_1)).
% 3.53/1.62  tff(f_164, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & m1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tmap_1)).
% 3.53/1.62  tff(f_79, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (~v2_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & v1_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_pre_topc)).
% 3.53/1.62  tff(f_183, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 3.53/1.62  tff(f_49, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 3.53/1.62  tff(f_155, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 3.53/1.62  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.53/1.62  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.53/1.62  tff(f_33, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.53/1.62  tff(f_69, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & v2_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_pre_topc)).
% 3.53/1.62  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 3.53/1.62  tff(f_128, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((~v2_struct_0(D) & v1_pre_topc(D)) & m1_pre_topc(D, A)) => ((D = k1_tsep_1(A, B, C)) <=> (u1_struct_0(D) = k2_xboole_0(u1_struct_0(B), u1_struct_0(C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tsep_1)).
% 3.53/1.62  tff(c_62, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_216])).
% 3.53/1.62  tff(c_14, plain, (![A_15]: (l1_struct_0(A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.53/1.62  tff(c_66, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_216])).
% 3.53/1.62  tff(c_50, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_216])).
% 3.53/1.62  tff(c_48, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_216])).
% 3.53/1.62  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_216])).
% 3.53/1.62  tff(c_315, plain, (![E_115, C_114, A_117, F_118, D_119, B_116]: (r1_funct_2(A_117, B_116, C_114, D_119, E_115, E_115) | ~m1_subset_1(F_118, k1_zfmisc_1(k2_zfmisc_1(C_114, D_119))) | ~v1_funct_2(F_118, C_114, D_119) | ~v1_funct_1(F_118) | ~m1_subset_1(E_115, k1_zfmisc_1(k2_zfmisc_1(A_117, B_116))) | ~v1_funct_2(E_115, A_117, B_116) | ~v1_funct_1(E_115) | v1_xboole_0(D_119) | v1_xboole_0(B_116))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.53/1.62  tff(c_317, plain, (![A_117, B_116, E_115]: (r1_funct_2(A_117, B_116, u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), E_115, E_115) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_115, k1_zfmisc_1(k2_zfmisc_1(A_117, B_116))) | ~v1_funct_2(E_115, A_117, B_116) | ~v1_funct_1(E_115) | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_116))), inference(resolution, [status(thm)], [c_46, c_315])).
% 3.53/1.62  tff(c_320, plain, (![A_117, B_116, E_115]: (r1_funct_2(A_117, B_116, u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), E_115, E_115) | ~m1_subset_1(E_115, k1_zfmisc_1(k2_zfmisc_1(A_117, B_116))) | ~v1_funct_2(E_115, A_117, B_116) | ~v1_funct_1(E_115) | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_116))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_317])).
% 3.53/1.62  tff(c_323, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_320])).
% 3.53/1.62  tff(c_16, plain, (![A_16]: (~v1_xboole_0(u1_struct_0(A_16)) | ~l1_struct_0(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.53/1.62  tff(c_326, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_323, c_16])).
% 3.53/1.62  tff(c_329, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_66, c_326])).
% 3.53/1.62  tff(c_332, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_329])).
% 3.53/1.62  tff(c_336, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_332])).
% 3.53/1.62  tff(c_338, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_320])).
% 3.53/1.62  tff(c_56, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_216])).
% 3.53/1.62  tff(c_52, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_216])).
% 3.53/1.62  tff(c_60, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_216])).
% 3.53/1.62  tff(c_54, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_216])).
% 3.53/1.62  tff(c_58, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_216])).
% 3.53/1.62  tff(c_203, plain, (![A_106, B_107]: (k1_tsep_1(A_106, B_107, B_107)=g1_pre_topc(u1_struct_0(B_107), u1_pre_topc(B_107)) | ~m1_pre_topc(B_107, A_106) | v2_struct_0(B_107) | ~l1_pre_topc(A_106) | ~v2_pre_topc(A_106) | v2_struct_0(A_106))), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.53/1.62  tff(c_211, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=k1_tsep_1('#skF_2', '#skF_3', '#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_52, c_203])).
% 3.53/1.62  tff(c_219, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=k1_tsep_1('#skF_2', '#skF_3', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_211])).
% 3.53/1.62  tff(c_220, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=k1_tsep_1('#skF_2', '#skF_3', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_219])).
% 3.53/1.62  tff(c_34, plain, (![B_57, A_55]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_57), u1_pre_topc(B_57)), A_55) | ~m1_pre_topc(B_57, A_55) | ~l1_pre_topc(A_55))), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.53/1.62  tff(c_236, plain, (![A_55]: (m1_pre_topc(k1_tsep_1('#skF_2', '#skF_3', '#skF_3'), A_55) | ~m1_pre_topc('#skF_3', A_55) | ~l1_pre_topc(A_55))), inference(superposition, [status(thm), theory('equality')], [c_220, c_34])).
% 3.53/1.62  tff(c_44, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_216])).
% 3.53/1.62  tff(c_109, plain, (![A_88]: (~v2_struct_0(g1_pre_topc(u1_struct_0(A_88), u1_pre_topc(A_88))) | ~l1_pre_topc(A_88) | v2_struct_0(A_88))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.53/1.62  tff(c_112, plain, (~v2_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_44, c_109])).
% 3.53/1.62  tff(c_114, plain, (~v2_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_112])).
% 3.53/1.62  tff(c_115, plain, (~v2_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_60, c_114])).
% 3.53/1.62  tff(c_225, plain, (~v2_struct_0(k1_tsep_1('#skF_2', '#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_220, c_115])).
% 3.53/1.62  tff(c_40, plain, (![A_61]: (m1_pre_topc(A_61, A_61) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_183])).
% 3.53/1.62  tff(c_64, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_216])).
% 3.53/1.62  tff(c_157, plain, (![A_97, B_98, C_99, D_100]: (k2_partfun1(A_97, B_98, C_99, D_100)=k7_relat_1(C_99, D_100) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))) | ~v1_funct_1(C_99))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.53/1.62  tff(c_159, plain, (![D_100]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_100)=k7_relat_1('#skF_4', D_100) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_46, c_157])).
% 3.53/1.62  tff(c_162, plain, (![D_100]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_100)=k7_relat_1('#skF_4', D_100))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_159])).
% 3.53/1.62  tff(c_401, plain, (![A_123, B_124, C_125, D_126]: (k2_partfun1(u1_struct_0(A_123), u1_struct_0(B_124), C_125, u1_struct_0(D_126))=k2_tmap_1(A_123, B_124, C_125, D_126) | ~m1_pre_topc(D_126, A_123) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_123), u1_struct_0(B_124)))) | ~v1_funct_2(C_125, u1_struct_0(A_123), u1_struct_0(B_124)) | ~v1_funct_1(C_125) | ~l1_pre_topc(B_124) | ~v2_pre_topc(B_124) | v2_struct_0(B_124) | ~l1_pre_topc(A_123) | ~v2_pre_topc(A_123) | v2_struct_0(A_123))), inference(cnfTransformation, [status(thm)], [f_155])).
% 3.53/1.62  tff(c_407, plain, (![D_126]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_126))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_126) | ~m1_pre_topc(D_126, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_46, c_401])).
% 3.53/1.62  tff(c_416, plain, (![D_126]: (k7_relat_1('#skF_4', u1_struct_0(D_126))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_126) | ~m1_pre_topc(D_126, '#skF_2') | v2_struct_0('#skF_1') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_64, c_62, c_50, c_48, c_162, c_407])).
% 3.53/1.62  tff(c_418, plain, (![D_127]: (k7_relat_1('#skF_4', u1_struct_0(D_127))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_127) | ~m1_pre_topc(D_127, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_60, c_66, c_416])).
% 3.53/1.62  tff(c_79, plain, (![C_77, A_78, B_79]: (v1_relat_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.53/1.62  tff(c_83, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_79])).
% 3.53/1.62  tff(c_84, plain, (![C_80, A_81, B_82]: (v4_relat_1(C_80, A_81) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.53/1.62  tff(c_88, plain, (v4_relat_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_46, c_84])).
% 3.53/1.62  tff(c_98, plain, (![B_86, A_87]: (k7_relat_1(B_86, A_87)=B_86 | ~v4_relat_1(B_86, A_87) | ~v1_relat_1(B_86))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.53/1.62  tff(c_101, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_2'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_88, c_98])).
% 3.53/1.62  tff(c_104, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_2'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_83, c_101])).
% 3.53/1.62  tff(c_424, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_2')='#skF_4' | ~m1_pre_topc('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_418, c_104])).
% 3.53/1.62  tff(c_436, plain, (~m1_pre_topc('#skF_2', '#skF_2')), inference(splitLeft, [status(thm)], [c_424])).
% 3.53/1.62  tff(c_439, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_40, c_436])).
% 3.53/1.62  tff(c_443, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_439])).
% 3.53/1.62  tff(c_445, plain, (m1_pre_topc('#skF_2', '#skF_2')), inference(splitRight, [status(thm)], [c_424])).
% 3.53/1.62  tff(c_488, plain, (![A_128]: (k1_tsep_1(A_128, A_128, A_128)=g1_pre_topc(u1_struct_0(A_128), u1_pre_topc(A_128)) | ~v2_pre_topc(A_128) | v2_struct_0(A_128) | ~l1_pre_topc(A_128))), inference(resolution, [status(thm)], [c_40, c_203])).
% 3.53/1.62  tff(c_226, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k1_tsep_1('#skF_2', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_220, c_44])).
% 3.53/1.62  tff(c_499, plain, (k1_tsep_1('#skF_2', '#skF_2', '#skF_2')=k1_tsep_1('#skF_2', '#skF_3', '#skF_3') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_488, c_226])).
% 3.53/1.62  tff(c_540, plain, (k1_tsep_1('#skF_2', '#skF_2', '#skF_2')=k1_tsep_1('#skF_2', '#skF_3', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_499])).
% 3.53/1.62  tff(c_541, plain, (k1_tsep_1('#skF_2', '#skF_2', '#skF_2')=k1_tsep_1('#skF_2', '#skF_3', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_60, c_540])).
% 3.53/1.62  tff(c_116, plain, (![A_89]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_89), u1_pre_topc(A_89))) | ~l1_pre_topc(A_89) | ~v2_pre_topc(A_89))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.53/1.62  tff(c_119, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_44, c_116])).
% 3.53/1.62  tff(c_121, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_119])).
% 3.53/1.62  tff(c_224, plain, (v1_pre_topc(k1_tsep_1('#skF_2', '#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_220, c_121])).
% 3.53/1.62  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.53/1.62  tff(c_341, plain, (![A_120, B_121, C_122]: (u1_struct_0(k1_tsep_1(A_120, B_121, C_122))=k2_xboole_0(u1_struct_0(B_121), u1_struct_0(C_122)) | ~m1_pre_topc(k1_tsep_1(A_120, B_121, C_122), A_120) | ~v1_pre_topc(k1_tsep_1(A_120, B_121, C_122)) | v2_struct_0(k1_tsep_1(A_120, B_121, C_122)) | ~m1_pre_topc(C_122, A_120) | v2_struct_0(C_122) | ~m1_pre_topc(B_121, A_120) | v2_struct_0(B_121) | ~l1_pre_topc(A_120) | v2_struct_0(A_120))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.53/1.62  tff(c_344, plain, (k2_xboole_0(u1_struct_0('#skF_3'), u1_struct_0('#skF_3'))=u1_struct_0(k1_tsep_1('#skF_2', '#skF_3', '#skF_3')) | ~v1_pre_topc(k1_tsep_1('#skF_2', '#skF_3', '#skF_3')) | v2_struct_0(k1_tsep_1('#skF_2', '#skF_3', '#skF_3')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_236, c_341])).
% 3.53/1.62  tff(c_350, plain, (u1_struct_0(k1_tsep_1('#skF_2', '#skF_3', '#skF_3'))=u1_struct_0('#skF_3') | v2_struct_0(k1_tsep_1('#skF_2', '#skF_3', '#skF_3')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_224, c_2, c_344])).
% 3.53/1.62  tff(c_351, plain, (u1_struct_0(k1_tsep_1('#skF_2', '#skF_3', '#skF_3'))=u1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_225, c_350])).
% 3.53/1.62  tff(c_30, plain, (![A_25, B_33, C_37]: (u1_struct_0(k1_tsep_1(A_25, B_33, C_37))=k2_xboole_0(u1_struct_0(B_33), u1_struct_0(C_37)) | ~m1_pre_topc(k1_tsep_1(A_25, B_33, C_37), A_25) | ~v1_pre_topc(k1_tsep_1(A_25, B_33, C_37)) | v2_struct_0(k1_tsep_1(A_25, B_33, C_37)) | ~m1_pre_topc(C_37, A_25) | v2_struct_0(C_37) | ~m1_pre_topc(B_33, A_25) | v2_struct_0(B_33) | ~l1_pre_topc(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.53/1.62  tff(c_555, plain, (k2_xboole_0(u1_struct_0('#skF_2'), u1_struct_0('#skF_2'))=u1_struct_0(k1_tsep_1('#skF_2', '#skF_2', '#skF_2')) | ~m1_pre_topc(k1_tsep_1('#skF_2', '#skF_3', '#skF_3'), '#skF_2') | ~v1_pre_topc(k1_tsep_1('#skF_2', '#skF_2', '#skF_2')) | v2_struct_0(k1_tsep_1('#skF_2', '#skF_2', '#skF_2')) | ~m1_pre_topc('#skF_2', '#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_2', '#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_541, c_30])).
% 3.53/1.62  tff(c_559, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~m1_pre_topc(k1_tsep_1('#skF_2', '#skF_3', '#skF_3'), '#skF_2') | v2_struct_0(k1_tsep_1('#skF_2', '#skF_3', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_445, c_445, c_541, c_224, c_541, c_351, c_541, c_2, c_555])).
% 3.53/1.62  tff(c_560, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~m1_pre_topc(k1_tsep_1('#skF_2', '#skF_3', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_60, c_225, c_559])).
% 3.53/1.62  tff(c_564, plain, (~m1_pre_topc(k1_tsep_1('#skF_2', '#skF_3', '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_560])).
% 3.53/1.62  tff(c_567, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_236, c_564])).
% 3.53/1.62  tff(c_574, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_567])).
% 3.53/1.62  tff(c_575, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_560])).
% 3.53/1.62  tff(c_583, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_575, c_48])).
% 3.53/1.62  tff(c_582, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_575, c_46])).
% 3.53/1.62  tff(c_337, plain, (![A_117, B_116, E_115]: (r1_funct_2(A_117, B_116, u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), E_115, E_115) | ~m1_subset_1(E_115, k1_zfmisc_1(k2_zfmisc_1(A_117, B_116))) | ~v1_funct_2(E_115, A_117, B_116) | ~v1_funct_1(E_115) | v1_xboole_0(B_116))), inference(splitRight, [status(thm)], [c_320])).
% 3.53/1.62  tff(c_668, plain, (![A_117, B_116, E_115]: (r1_funct_2(A_117, B_116, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), E_115, E_115) | ~m1_subset_1(E_115, k1_zfmisc_1(k2_zfmisc_1(A_117, B_116))) | ~v1_funct_2(E_115, A_117, B_116) | ~v1_funct_1(E_115) | v1_xboole_0(B_116))), inference(demodulation, [status(thm), theory('equality')], [c_575, c_337])).
% 3.53/1.62  tff(c_417, plain, (![D_126]: (k7_relat_1('#skF_4', u1_struct_0(D_126))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_126) | ~m1_pre_topc(D_126, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_60, c_66, c_416])).
% 3.53/1.62  tff(c_580, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_575, c_104])).
% 3.53/1.62  tff(c_661, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4' | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_417, c_580])).
% 3.53/1.62  tff(c_667, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_661])).
% 3.53/1.62  tff(c_42, plain, (~r1_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_216])).
% 3.53/1.62  tff(c_579, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_575, c_42])).
% 3.53/1.62  tff(c_966, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_667, c_579])).
% 3.53/1.62  tff(c_969, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_668, c_966])).
% 3.53/1.62  tff(c_972, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_583, c_582, c_969])).
% 3.53/1.62  tff(c_974, plain, $false, inference(negUnitSimplification, [status(thm)], [c_338, c_972])).
% 3.53/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.62  
% 3.53/1.62  Inference rules
% 3.53/1.62  ----------------------
% 3.53/1.62  #Ref     : 1
% 3.53/1.62  #Sup     : 200
% 3.53/1.62  #Fact    : 0
% 3.53/1.62  #Define  : 0
% 3.53/1.62  #Split   : 7
% 3.53/1.62  #Chain   : 0
% 3.53/1.62  #Close   : 0
% 3.53/1.62  
% 3.53/1.62  Ordering : KBO
% 3.53/1.62  
% 3.53/1.62  Simplification rules
% 3.53/1.62  ----------------------
% 3.53/1.62  #Subsume      : 22
% 3.53/1.62  #Demod        : 293
% 3.53/1.62  #Tautology    : 77
% 3.53/1.62  #SimpNegUnit  : 53
% 3.53/1.62  #BackRed      : 17
% 3.53/1.62  
% 3.53/1.62  #Partial instantiations: 0
% 3.53/1.62  #Strategies tried      : 1
% 3.53/1.62  
% 3.53/1.62  Timing (in seconds)
% 3.53/1.62  ----------------------
% 3.53/1.62  Preprocessing        : 0.36
% 3.53/1.62  Parsing              : 0.19
% 3.53/1.62  CNF conversion       : 0.03
% 3.53/1.62  Main loop            : 0.44
% 3.53/1.62  Inferencing          : 0.14
% 3.53/1.62  Reduction            : 0.16
% 3.53/1.62  Demodulation         : 0.11
% 3.53/1.62  BG Simplification    : 0.03
% 3.53/1.62  Subsumption          : 0.08
% 3.53/1.62  Abstraction          : 0.02
% 3.53/1.62  MUC search           : 0.00
% 3.53/1.62  Cooper               : 0.00
% 3.53/1.62  Total                : 0.84
% 3.53/1.62  Index Insertion      : 0.00
% 3.53/1.62  Index Deletion       : 0.00
% 3.53/1.62  Index Matching       : 0.00
% 3.53/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
