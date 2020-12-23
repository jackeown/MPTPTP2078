%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:40 EST 2020

% Result     : Theorem 4.17s
% Output     : CNFRefutation 4.17s
% Verified   : 
% Statistics : Number of formulae       :  195 (61008 expanded)
%              Number of leaves         :   48 (21233 expanded)
%              Depth                    :   36
%              Number of atoms          :  440 (175679 expanded)
%              Number of equality atoms :  100 (37604 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_186,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_struct_0(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( ( k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                    & v2_funct_1(C) )
                 => r2_funct_2(u1_struct_0(A),u1_struct_0(B),k2_tops_2(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)),C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).

tff(f_144,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_152,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

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

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_108,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_124,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(f_140,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(C)
          & k2_relset_1(A,B,C) = B )
       => ( v1_funct_1(k2_funct_1(C))
          & v1_funct_2(k2_funct_1(C),B,A)
          & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_60,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_76,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_164,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(c_62,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_68,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_70,plain,(
    ! [A_45] :
      ( u1_struct_0(A_45) = k2_struct_0(A_45)
      | ~ l1_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_78,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_70])).

tff(c_64,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_77,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_70])).

tff(c_58,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_101,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_77,c_58])).

tff(c_204,plain,(
    ! [A_67,B_68,C_69] :
      ( k2_relset_1(A_67,B_68,C_69) = k2_relat_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_208,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_101,c_204])).

tff(c_56,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_118,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_77,c_56])).

tff(c_209,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_118])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_88,plain,(
    ! [A_46] :
      ( ~ v1_xboole_0(u1_struct_0(A_46))
      | ~ l1_struct_0(A_46)
      | v2_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_94,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_88])).

tff(c_98,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_94])).

tff(c_99,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_98])).

tff(c_218,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_99])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_111,plain,(
    ! [B_48,A_49] :
      ( v1_relat_1(B_48)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_49))
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_114,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_101,c_111])).

tff(c_117,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_114])).

tff(c_130,plain,(
    ! [C_55,A_56,B_57] :
      ( v4_relat_1(C_55,A_56)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_134,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_101,c_130])).

tff(c_196,plain,(
    ! [B_65,A_66] :
      ( k1_relat_1(B_65) = A_66
      | ~ v1_partfun1(B_65,A_66)
      | ~ v4_relat_1(B_65,A_66)
      | ~ v1_relat_1(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_199,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_134,c_196])).

tff(c_202,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_199])).

tff(c_203,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_202])).

tff(c_60,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_87,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_77,c_60])).

tff(c_219,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_87])).

tff(c_217,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_101])).

tff(c_272,plain,(
    ! [C_72,A_73,B_74] :
      ( v1_partfun1(C_72,A_73)
      | ~ v1_funct_2(C_72,A_73,B_74)
      | ~ v1_funct_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74)))
      | v1_xboole_0(B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_275,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_217,c_272])).

tff(c_278,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_219,c_275])).

tff(c_280,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_218,c_203,c_278])).

tff(c_281,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_202])).

tff(c_288,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_101])).

tff(c_26,plain,(
    ! [A_18,B_19,C_20] :
      ( k2_relset_1(A_18,B_19,C_20) = k2_relat_1(C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_354,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_288,c_26])).

tff(c_287,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_118])).

tff(c_366,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_287])).

tff(c_290,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_87])).

tff(c_373,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_366,c_290])).

tff(c_372,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_366,c_288])).

tff(c_429,plain,(
    ! [A_80,B_81,D_82] :
      ( r2_funct_2(A_80,B_81,D_82,D_82)
      | ~ m1_subset_1(D_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81)))
      | ~ v1_funct_2(D_82,A_80,B_81)
      | ~ v1_funct_1(D_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_431,plain,
    ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_372,c_429])).

tff(c_434,plain,(
    r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_373,c_431])).

tff(c_54,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_371,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_366,c_354])).

tff(c_465,plain,(
    ! [C_88,A_89,B_90] :
      ( v1_funct_1(k2_funct_1(C_88))
      | k2_relset_1(A_89,B_90,C_88) != B_90
      | ~ v2_funct_1(C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90)))
      | ~ v1_funct_2(C_88,A_89,B_90)
      | ~ v1_funct_1(C_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_468,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_372,c_465])).

tff(c_471,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_373,c_54,c_371,c_468])).

tff(c_489,plain,(
    ! [C_91,B_92,A_93] :
      ( v1_funct_2(k2_funct_1(C_91),B_92,A_93)
      | k2_relset_1(A_93,B_92,C_91) != B_92
      | ~ v2_funct_1(C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_93,B_92)))
      | ~ v1_funct_2(C_91,A_93,B_92)
      | ~ v1_funct_1(C_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_492,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_372,c_489])).

tff(c_495,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_373,c_54,c_371,c_492])).

tff(c_10,plain,(
    ! [B_10,A_9] :
      ( k7_relat_1(B_10,A_9) = B_10
      | ~ v4_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_137,plain,
    ( k7_relat_1('#skF_3',k2_struct_0('#skF_1')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_134,c_10])).

tff(c_140,plain,(
    k7_relat_1('#skF_3',k2_struct_0('#skF_1')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_137])).

tff(c_284,plain,(
    k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_140])).

tff(c_6,plain,(
    ! [B_7,A_6] :
      ( k2_relat_1(k7_relat_1(B_7,A_6)) = k9_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_156,plain,
    ( k9_relat_1('#skF_3',k2_struct_0('#skF_1')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_6])).

tff(c_160,plain,(
    k9_relat_1('#skF_3',k2_struct_0('#skF_1')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_156])).

tff(c_283,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_160])).

tff(c_141,plain,(
    ! [B_58,A_59] :
      ( k2_relat_1(k7_relat_1(B_58,A_59)) = k9_relat_1(B_58,A_59)
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_8] :
      ( k10_relat_1(A_8,k2_relat_1(A_8)) = k1_relat_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_443,plain,(
    ! [B_86,A_87] :
      ( k10_relat_1(k7_relat_1(B_86,A_87),k9_relat_1(B_86,A_87)) = k1_relat_1(k7_relat_1(B_86,A_87))
      | ~ v1_relat_1(k7_relat_1(B_86,A_87))
      | ~ v1_relat_1(B_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_8])).

tff(c_458,plain,
    ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',k1_relat_1('#skF_3'))) = k1_relat_1(k7_relat_1('#skF_3',k1_relat_1('#skF_3')))
    | ~ v1_relat_1(k7_relat_1('#skF_3',k1_relat_1('#skF_3')))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_284,c_443])).

tff(c_464,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_117,c_284,c_283,c_284,c_458])).

tff(c_18,plain,(
    ! [B_13,A_12] :
      ( k9_relat_1(k2_funct_1(B_13),A_12) = k10_relat_1(B_13,A_12)
      | ~ v2_funct_1(B_13)
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_16,plain,(
    ! [A_11] :
      ( v1_relat_1(k2_funct_1(A_11))
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_12,plain,(
    ! [A_11] :
      ( v2_funct_1(k2_funct_1(A_11))
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_20,plain,(
    ! [A_14] :
      ( k2_funct_1(k2_funct_1(A_14)) = A_14
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_391,plain,(
    ! [B_78,A_79] :
      ( k9_relat_1(k2_funct_1(B_78),A_79) = k10_relat_1(B_78,A_79)
      | ~ v2_funct_1(B_78)
      | ~ v1_funct_1(B_78)
      | ~ v1_relat_1(B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_496,plain,(
    ! [A_94,A_95] :
      ( k10_relat_1(k2_funct_1(A_94),A_95) = k9_relat_1(A_94,A_95)
      | ~ v2_funct_1(k2_funct_1(A_94))
      | ~ v1_funct_1(k2_funct_1(A_94))
      | ~ v1_relat_1(k2_funct_1(A_94))
      | ~ v2_funct_1(A_94)
      | ~ v1_funct_1(A_94)
      | ~ v1_relat_1(A_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_391])).

tff(c_502,plain,(
    ! [A_96,A_97] :
      ( k10_relat_1(k2_funct_1(A_96),A_97) = k9_relat_1(A_96,A_97)
      | ~ v1_funct_1(k2_funct_1(A_96))
      | ~ v1_relat_1(k2_funct_1(A_96))
      | ~ v2_funct_1(A_96)
      | ~ v1_funct_1(A_96)
      | ~ v1_relat_1(A_96) ) ),
    inference(resolution,[status(thm)],[c_12,c_496])).

tff(c_508,plain,(
    ! [A_98,A_99] :
      ( k10_relat_1(k2_funct_1(A_98),A_99) = k9_relat_1(A_98,A_99)
      | ~ v1_funct_1(k2_funct_1(A_98))
      | ~ v2_funct_1(A_98)
      | ~ v1_funct_1(A_98)
      | ~ v1_relat_1(A_98) ) ),
    inference(resolution,[status(thm)],[c_16,c_502])).

tff(c_510,plain,(
    ! [A_99] :
      ( k10_relat_1(k2_funct_1('#skF_3'),A_99) = k9_relat_1('#skF_3',A_99)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_471,c_508])).

tff(c_519,plain,(
    ! [A_100] : k10_relat_1(k2_funct_1('#skF_3'),A_100) = k9_relat_1('#skF_3',A_100) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_62,c_54,c_510])).

tff(c_526,plain,
    ( k9_relat_1('#skF_3',k2_relat_1(k2_funct_1('#skF_3'))) = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_519,c_8])).

tff(c_548,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_526])).

tff(c_551,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_548])).

tff(c_555,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_62,c_54,c_551])).

tff(c_557,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_526])).

tff(c_637,plain,(
    ! [C_107,B_108,A_109] :
      ( m1_subset_1(k2_funct_1(C_107),k1_zfmisc_1(k2_zfmisc_1(B_108,A_109)))
      | k2_relset_1(A_109,B_108,C_107) != B_108
      | ~ v2_funct_1(C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_109,B_108)))
      | ~ v1_funct_2(C_107,A_109,B_108)
      | ~ v1_funct_1(C_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_24,plain,(
    ! [C_17,A_15,B_16] :
      ( v4_relat_1(C_17,A_15)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_809,plain,(
    ! [C_132,B_133,A_134] :
      ( v4_relat_1(k2_funct_1(C_132),B_133)
      | k2_relset_1(A_134,B_133,C_132) != B_133
      | ~ v2_funct_1(C_132)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_134,B_133)))
      | ~ v1_funct_2(C_132,A_134,B_133)
      | ~ v1_funct_1(C_132) ) ),
    inference(resolution,[status(thm)],[c_637,c_24])).

tff(c_815,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_372,c_809])).

tff(c_819,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_373,c_54,c_371,c_815])).

tff(c_832,plain,
    ( k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_819,c_10])).

tff(c_838,plain,(
    k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_557,c_832])).

tff(c_845,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_838,c_6])).

tff(c_851,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_557,c_845])).

tff(c_863,plain,
    ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_851])).

tff(c_871,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_62,c_54,c_464,c_863])).

tff(c_918,plain,(
    ! [B_139,A_140,C_141] :
      ( k2_relset_1(B_139,A_140,k2_funct_1(C_141)) = k2_relat_1(k2_funct_1(C_141))
      | k2_relset_1(A_140,B_139,C_141) != B_139
      | ~ v2_funct_1(C_141)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_140,B_139)))
      | ~ v1_funct_2(C_141,A_140,B_139)
      | ~ v1_funct_1(C_141) ) ),
    inference(resolution,[status(thm)],[c_637,c_26])).

tff(c_924,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_372,c_918])).

tff(c_928,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_373,c_54,c_371,c_924])).

tff(c_947,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_871,c_928])).

tff(c_517,plain,(
    ! [A_99] : k10_relat_1(k2_funct_1('#skF_3'),A_99) = k9_relat_1('#skF_3',A_99) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_62,c_54,c_510])).

tff(c_987,plain,(
    ! [B_145,A_146] :
      ( k10_relat_1(k7_relat_1(k2_funct_1(B_145),A_146),k10_relat_1(B_145,A_146)) = k1_relat_1(k7_relat_1(k2_funct_1(B_145),A_146))
      | ~ v1_relat_1(k7_relat_1(k2_funct_1(B_145),A_146))
      | ~ v1_relat_1(k2_funct_1(B_145))
      | ~ v2_funct_1(B_145)
      | ~ v1_funct_1(B_145)
      | ~ v1_relat_1(B_145) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_443])).

tff(c_1008,plain,(
    ! [A_99] :
      ( k10_relat_1(k7_relat_1(k2_funct_1(k2_funct_1('#skF_3')),A_99),k9_relat_1('#skF_3',A_99)) = k1_relat_1(k7_relat_1(k2_funct_1(k2_funct_1('#skF_3')),A_99))
      | ~ v1_relat_1(k7_relat_1(k2_funct_1(k2_funct_1('#skF_3')),A_99))
      | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
      | ~ v2_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_517,c_987])).

tff(c_1026,plain,(
    ! [A_99] :
      ( k10_relat_1(k7_relat_1(k2_funct_1(k2_funct_1('#skF_3')),A_99),k9_relat_1('#skF_3',A_99)) = k1_relat_1(k7_relat_1(k2_funct_1(k2_funct_1('#skF_3')),A_99))
      | ~ v1_relat_1(k7_relat_1(k2_funct_1(k2_funct_1('#skF_3')),A_99))
      | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
      | ~ v2_funct_1(k2_funct_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_557,c_471,c_1008])).

tff(c_1038,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1026])).

tff(c_1041,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_1038])).

tff(c_1045,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_62,c_54,c_1041])).

tff(c_1047,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1026])).

tff(c_14,plain,(
    ! [A_11] :
      ( v1_funct_1(k2_funct_1(A_11))
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_569,plain,(
    ! [A_104,A_105] :
      ( k10_relat_1(k2_funct_1(A_104),A_105) = k9_relat_1(A_104,A_105)
      | ~ v2_funct_1(A_104)
      | ~ v1_funct_1(A_104)
      | ~ v1_relat_1(A_104) ) ),
    inference(resolution,[status(thm)],[c_14,c_508])).

tff(c_602,plain,(
    ! [A_106] :
      ( k9_relat_1(A_106,k2_relat_1(k2_funct_1(A_106))) = k1_relat_1(k2_funct_1(A_106))
      | ~ v1_relat_1(k2_funct_1(A_106))
      | ~ v2_funct_1(A_106)
      | ~ v1_funct_1(A_106)
      | ~ v1_relat_1(A_106) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_569,c_8])).

tff(c_1029,plain,(
    ! [A_147] :
      ( k9_relat_1(k2_funct_1(A_147),k2_relat_1(A_147)) = k1_relat_1(k2_funct_1(k2_funct_1(A_147)))
      | ~ v1_relat_1(k2_funct_1(k2_funct_1(A_147)))
      | ~ v2_funct_1(k2_funct_1(A_147))
      | ~ v1_funct_1(k2_funct_1(A_147))
      | ~ v1_relat_1(k2_funct_1(A_147))
      | ~ v2_funct_1(A_147)
      | ~ v1_funct_1(A_147)
      | ~ v1_relat_1(A_147) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_602])).

tff(c_1048,plain,(
    ! [A_148] :
      ( k9_relat_1(k2_funct_1(A_148),k2_relat_1(A_148)) = k1_relat_1(k2_funct_1(k2_funct_1(A_148)))
      | ~ v2_funct_1(A_148)
      | ~ v1_funct_1(A_148)
      | ~ v1_relat_1(A_148)
      | ~ v2_funct_1(k2_funct_1(A_148))
      | ~ v1_funct_1(k2_funct_1(A_148))
      | ~ v1_relat_1(k2_funct_1(A_148)) ) ),
    inference(resolution,[status(thm)],[c_16,c_1029])).

tff(c_930,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_871,c_851])).

tff(c_1054,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1048,c_930])).

tff(c_1082,plain,(
    k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_557,c_471,c_1047,c_117,c_62,c_54,c_1054])).

tff(c_32,plain,(
    ! [B_26] :
      ( v1_partfun1(B_26,k1_relat_1(B_26))
      | ~ v4_relat_1(B_26,k1_relat_1(B_26))
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1091,plain,
    ( v1_partfun1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v4_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1082,c_32])).

tff(c_1097,plain,
    ( v1_partfun1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3'))
    | ~ v4_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1082,c_1091])).

tff(c_1114,plain,(
    ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_1097])).

tff(c_1117,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1114])).

tff(c_1123,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_62,c_54,c_117,c_1117])).

tff(c_1125,plain,(
    v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_1097])).

tff(c_285,plain,(
    v4_relat_1('#skF_3',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_134])).

tff(c_1124,plain,
    ( ~ v4_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3'))
    | v1_partfun1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1097])).

tff(c_1159,plain,(
    ~ v4_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1124])).

tff(c_1162,plain,
    ( ~ v4_relat_1('#skF_3',k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1159])).

tff(c_1165,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_62,c_54,c_285,c_1162])).

tff(c_1167,plain,(
    v4_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1124])).

tff(c_1178,plain,
    ( k7_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_1167,c_10])).

tff(c_1187,plain,(
    k7_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1125,c_1178])).

tff(c_1206,plain,
    ( k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1187])).

tff(c_1218,plain,(
    k2_funct_1(k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_62,c_54,c_284,c_1206])).

tff(c_50,plain,(
    ! [A_36,B_37,C_38] :
      ( k2_tops_2(A_36,B_37,C_38) = k2_funct_1(C_38)
      | ~ v2_funct_1(C_38)
      | k2_relset_1(A_36,B_37,C_38) != B_37
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37)))
      | ~ v1_funct_2(C_38,A_36,B_37)
      | ~ v1_funct_1(C_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_1803,plain,(
    ! [B_184,A_185,C_186] :
      ( k2_tops_2(B_184,A_185,k2_funct_1(C_186)) = k2_funct_1(k2_funct_1(C_186))
      | ~ v2_funct_1(k2_funct_1(C_186))
      | k2_relset_1(B_184,A_185,k2_funct_1(C_186)) != A_185
      | ~ v1_funct_2(k2_funct_1(C_186),B_184,A_185)
      | ~ v1_funct_1(k2_funct_1(C_186))
      | k2_relset_1(A_185,B_184,C_186) != B_184
      | ~ v2_funct_1(C_186)
      | ~ m1_subset_1(C_186,k1_zfmisc_1(k2_zfmisc_1(A_185,B_184)))
      | ~ v1_funct_2(C_186,A_185,B_184)
      | ~ v1_funct_1(C_186) ) ),
    inference(resolution,[status(thm)],[c_637,c_50])).

tff(c_1812,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_372,c_1803])).

tff(c_1819,plain,(
    k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_373,c_54,c_371,c_471,c_495,c_947,c_1047,c_1218,c_1812])).

tff(c_536,plain,(
    ! [A_101,B_102,C_103] :
      ( k2_tops_2(A_101,B_102,C_103) = k2_funct_1(C_103)
      | ~ v2_funct_1(C_103)
      | k2_relset_1(A_101,B_102,C_103) != B_102
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102)))
      | ~ v1_funct_2(C_103,A_101,B_102)
      | ~ v1_funct_1(C_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_539,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_372,c_536])).

tff(c_542,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_373,c_371,c_54,c_539])).

tff(c_52,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_123,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_78,c_78,c_77,c_77,c_77,c_52])).

tff(c_286,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_281,c_281,c_123])).

tff(c_407,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_366,c_366,c_366,c_286])).

tff(c_543,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_542,c_407])).

tff(c_1820,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1819,c_543])).

tff(c_1823,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_434,c_1820])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:55:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.17/1.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.17/1.74  
% 4.17/1.74  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.17/1.75  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 4.17/1.75  
% 4.17/1.75  %Foreground sorts:
% 4.17/1.75  
% 4.17/1.75  
% 4.17/1.75  %Background operators:
% 4.17/1.75  
% 4.17/1.75  
% 4.17/1.75  %Foreground operators:
% 4.17/1.75  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.17/1.75  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.17/1.75  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.17/1.75  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.17/1.75  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.17/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.17/1.75  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.17/1.75  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.17/1.75  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 4.17/1.75  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.17/1.75  tff('#skF_2', type, '#skF_2': $i).
% 4.17/1.75  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.17/1.75  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.17/1.75  tff('#skF_3', type, '#skF_3': $i).
% 4.17/1.75  tff('#skF_1', type, '#skF_1': $i).
% 4.17/1.75  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.17/1.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.17/1.75  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.17/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.17/1.75  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.17/1.75  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.17/1.75  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.17/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.17/1.75  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.17/1.75  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.17/1.75  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.17/1.75  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.17/1.75  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.17/1.75  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 4.17/1.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.17/1.75  
% 4.17/1.77  tff(f_186, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tops_2)).
% 4.17/1.77  tff(f_144, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 4.17/1.77  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.17/1.77  tff(f_152, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.17/1.77  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.17/1.77  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.17/1.77  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.17/1.77  tff(f_108, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 4.17/1.77  tff(f_100, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 4.17/1.77  tff(f_124, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 4.17/1.77  tff(f_140, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 4.17/1.77  tff(f_48, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 4.17/1.77  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 4.17/1.77  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 4.17/1.77  tff(f_68, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_1)).
% 4.17/1.77  tff(f_60, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_funct_1)).
% 4.17/1.77  tff(f_76, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 4.17/1.77  tff(f_164, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 4.17/1.77  tff(c_62, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.17/1.77  tff(c_68, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.17/1.77  tff(c_70, plain, (![A_45]: (u1_struct_0(A_45)=k2_struct_0(A_45) | ~l1_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.17/1.77  tff(c_78, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_68, c_70])).
% 4.17/1.77  tff(c_64, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.17/1.77  tff(c_77, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_64, c_70])).
% 4.17/1.77  tff(c_58, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.17/1.77  tff(c_101, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_77, c_58])).
% 4.17/1.77  tff(c_204, plain, (![A_67, B_68, C_69]: (k2_relset_1(A_67, B_68, C_69)=k2_relat_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.17/1.77  tff(c_208, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_101, c_204])).
% 4.17/1.77  tff(c_56, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.17/1.77  tff(c_118, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_77, c_56])).
% 4.17/1.77  tff(c_209, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_208, c_118])).
% 4.17/1.77  tff(c_66, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.17/1.77  tff(c_88, plain, (![A_46]: (~v1_xboole_0(u1_struct_0(A_46)) | ~l1_struct_0(A_46) | v2_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.17/1.77  tff(c_94, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_77, c_88])).
% 4.17/1.77  tff(c_98, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_94])).
% 4.17/1.77  tff(c_99, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_66, c_98])).
% 4.17/1.77  tff(c_218, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_209, c_99])).
% 4.17/1.77  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.17/1.77  tff(c_111, plain, (![B_48, A_49]: (v1_relat_1(B_48) | ~m1_subset_1(B_48, k1_zfmisc_1(A_49)) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.17/1.78  tff(c_114, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_101, c_111])).
% 4.17/1.78  tff(c_117, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_114])).
% 4.17/1.78  tff(c_130, plain, (![C_55, A_56, B_57]: (v4_relat_1(C_55, A_56) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.17/1.78  tff(c_134, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_101, c_130])).
% 4.17/1.78  tff(c_196, plain, (![B_65, A_66]: (k1_relat_1(B_65)=A_66 | ~v1_partfun1(B_65, A_66) | ~v4_relat_1(B_65, A_66) | ~v1_relat_1(B_65))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.17/1.78  tff(c_199, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_134, c_196])).
% 4.17/1.78  tff(c_202, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_199])).
% 4.17/1.78  tff(c_203, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_202])).
% 4.17/1.78  tff(c_60, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.17/1.78  tff(c_87, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_77, c_60])).
% 4.17/1.78  tff(c_219, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_209, c_87])).
% 4.17/1.78  tff(c_217, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_209, c_101])).
% 4.17/1.78  tff(c_272, plain, (![C_72, A_73, B_74]: (v1_partfun1(C_72, A_73) | ~v1_funct_2(C_72, A_73, B_74) | ~v1_funct_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))) | v1_xboole_0(B_74))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.17/1.78  tff(c_275, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_217, c_272])).
% 4.17/1.78  tff(c_278, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_219, c_275])).
% 4.17/1.78  tff(c_280, plain, $false, inference(negUnitSimplification, [status(thm)], [c_218, c_203, c_278])).
% 4.17/1.78  tff(c_281, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_202])).
% 4.17/1.78  tff(c_288, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_281, c_101])).
% 4.17/1.78  tff(c_26, plain, (![A_18, B_19, C_20]: (k2_relset_1(A_18, B_19, C_20)=k2_relat_1(C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.17/1.78  tff(c_354, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_288, c_26])).
% 4.17/1.78  tff(c_287, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_281, c_118])).
% 4.17/1.78  tff(c_366, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_354, c_287])).
% 4.17/1.78  tff(c_290, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_281, c_87])).
% 4.17/1.78  tff(c_373, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_366, c_290])).
% 4.17/1.78  tff(c_372, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_366, c_288])).
% 4.17/1.78  tff(c_429, plain, (![A_80, B_81, D_82]: (r2_funct_2(A_80, B_81, D_82, D_82) | ~m1_subset_1(D_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))) | ~v1_funct_2(D_82, A_80, B_81) | ~v1_funct_1(D_82))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.17/1.78  tff(c_431, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_372, c_429])).
% 4.17/1.78  tff(c_434, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_373, c_431])).
% 4.17/1.78  tff(c_54, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.17/1.78  tff(c_371, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_366, c_354])).
% 4.17/1.78  tff(c_465, plain, (![C_88, A_89, B_90]: (v1_funct_1(k2_funct_1(C_88)) | k2_relset_1(A_89, B_90, C_88)!=B_90 | ~v2_funct_1(C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))) | ~v1_funct_2(C_88, A_89, B_90) | ~v1_funct_1(C_88))), inference(cnfTransformation, [status(thm)], [f_140])).
% 4.17/1.78  tff(c_468, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_372, c_465])).
% 4.17/1.78  tff(c_471, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_373, c_54, c_371, c_468])).
% 4.17/1.78  tff(c_489, plain, (![C_91, B_92, A_93]: (v1_funct_2(k2_funct_1(C_91), B_92, A_93) | k2_relset_1(A_93, B_92, C_91)!=B_92 | ~v2_funct_1(C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_93, B_92))) | ~v1_funct_2(C_91, A_93, B_92) | ~v1_funct_1(C_91))), inference(cnfTransformation, [status(thm)], [f_140])).
% 4.17/1.78  tff(c_492, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_372, c_489])).
% 4.17/1.78  tff(c_495, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_373, c_54, c_371, c_492])).
% 4.17/1.78  tff(c_10, plain, (![B_10, A_9]: (k7_relat_1(B_10, A_9)=B_10 | ~v4_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.17/1.78  tff(c_137, plain, (k7_relat_1('#skF_3', k2_struct_0('#skF_1'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_134, c_10])).
% 4.17/1.78  tff(c_140, plain, (k7_relat_1('#skF_3', k2_struct_0('#skF_1'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_117, c_137])).
% 4.17/1.78  tff(c_284, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_281, c_140])).
% 4.17/1.78  tff(c_6, plain, (![B_7, A_6]: (k2_relat_1(k7_relat_1(B_7, A_6))=k9_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.17/1.78  tff(c_156, plain, (k9_relat_1('#skF_3', k2_struct_0('#skF_1'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_140, c_6])).
% 4.17/1.78  tff(c_160, plain, (k9_relat_1('#skF_3', k2_struct_0('#skF_1'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_117, c_156])).
% 4.17/1.78  tff(c_283, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_281, c_160])).
% 4.17/1.78  tff(c_141, plain, (![B_58, A_59]: (k2_relat_1(k7_relat_1(B_58, A_59))=k9_relat_1(B_58, A_59) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.17/1.78  tff(c_8, plain, (![A_8]: (k10_relat_1(A_8, k2_relat_1(A_8))=k1_relat_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.17/1.78  tff(c_443, plain, (![B_86, A_87]: (k10_relat_1(k7_relat_1(B_86, A_87), k9_relat_1(B_86, A_87))=k1_relat_1(k7_relat_1(B_86, A_87)) | ~v1_relat_1(k7_relat_1(B_86, A_87)) | ~v1_relat_1(B_86))), inference(superposition, [status(thm), theory('equality')], [c_141, c_8])).
% 4.17/1.78  tff(c_458, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', k1_relat_1('#skF_3')))=k1_relat_1(k7_relat_1('#skF_3', k1_relat_1('#skF_3'))) | ~v1_relat_1(k7_relat_1('#skF_3', k1_relat_1('#skF_3'))) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_284, c_443])).
% 4.17/1.78  tff(c_464, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_117, c_117, c_284, c_283, c_284, c_458])).
% 4.17/1.78  tff(c_18, plain, (![B_13, A_12]: (k9_relat_1(k2_funct_1(B_13), A_12)=k10_relat_1(B_13, A_12) | ~v2_funct_1(B_13) | ~v1_funct_1(B_13) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.17/1.78  tff(c_16, plain, (![A_11]: (v1_relat_1(k2_funct_1(A_11)) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.17/1.78  tff(c_12, plain, (![A_11]: (v2_funct_1(k2_funct_1(A_11)) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.17/1.78  tff(c_20, plain, (![A_14]: (k2_funct_1(k2_funct_1(A_14))=A_14 | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.17/1.78  tff(c_391, plain, (![B_78, A_79]: (k9_relat_1(k2_funct_1(B_78), A_79)=k10_relat_1(B_78, A_79) | ~v2_funct_1(B_78) | ~v1_funct_1(B_78) | ~v1_relat_1(B_78))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.17/1.78  tff(c_496, plain, (![A_94, A_95]: (k10_relat_1(k2_funct_1(A_94), A_95)=k9_relat_1(A_94, A_95) | ~v2_funct_1(k2_funct_1(A_94)) | ~v1_funct_1(k2_funct_1(A_94)) | ~v1_relat_1(k2_funct_1(A_94)) | ~v2_funct_1(A_94) | ~v1_funct_1(A_94) | ~v1_relat_1(A_94))), inference(superposition, [status(thm), theory('equality')], [c_20, c_391])).
% 4.17/1.78  tff(c_502, plain, (![A_96, A_97]: (k10_relat_1(k2_funct_1(A_96), A_97)=k9_relat_1(A_96, A_97) | ~v1_funct_1(k2_funct_1(A_96)) | ~v1_relat_1(k2_funct_1(A_96)) | ~v2_funct_1(A_96) | ~v1_funct_1(A_96) | ~v1_relat_1(A_96))), inference(resolution, [status(thm)], [c_12, c_496])).
% 4.17/1.78  tff(c_508, plain, (![A_98, A_99]: (k10_relat_1(k2_funct_1(A_98), A_99)=k9_relat_1(A_98, A_99) | ~v1_funct_1(k2_funct_1(A_98)) | ~v2_funct_1(A_98) | ~v1_funct_1(A_98) | ~v1_relat_1(A_98))), inference(resolution, [status(thm)], [c_16, c_502])).
% 4.17/1.78  tff(c_510, plain, (![A_99]: (k10_relat_1(k2_funct_1('#skF_3'), A_99)=k9_relat_1('#skF_3', A_99) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_471, c_508])).
% 4.17/1.78  tff(c_519, plain, (![A_100]: (k10_relat_1(k2_funct_1('#skF_3'), A_100)=k9_relat_1('#skF_3', A_100))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_62, c_54, c_510])).
% 4.17/1.78  tff(c_526, plain, (k9_relat_1('#skF_3', k2_relat_1(k2_funct_1('#skF_3')))=k1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_519, c_8])).
% 4.17/1.78  tff(c_548, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_526])).
% 4.17/1.78  tff(c_551, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_16, c_548])).
% 4.17/1.78  tff(c_555, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_117, c_62, c_54, c_551])).
% 4.17/1.78  tff(c_557, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_526])).
% 4.17/1.78  tff(c_637, plain, (![C_107, B_108, A_109]: (m1_subset_1(k2_funct_1(C_107), k1_zfmisc_1(k2_zfmisc_1(B_108, A_109))) | k2_relset_1(A_109, B_108, C_107)!=B_108 | ~v2_funct_1(C_107) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_109, B_108))) | ~v1_funct_2(C_107, A_109, B_108) | ~v1_funct_1(C_107))), inference(cnfTransformation, [status(thm)], [f_140])).
% 4.17/1.78  tff(c_24, plain, (![C_17, A_15, B_16]: (v4_relat_1(C_17, A_15) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.17/1.78  tff(c_809, plain, (![C_132, B_133, A_134]: (v4_relat_1(k2_funct_1(C_132), B_133) | k2_relset_1(A_134, B_133, C_132)!=B_133 | ~v2_funct_1(C_132) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_134, B_133))) | ~v1_funct_2(C_132, A_134, B_133) | ~v1_funct_1(C_132))), inference(resolution, [status(thm)], [c_637, c_24])).
% 4.17/1.78  tff(c_815, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_372, c_809])).
% 4.17/1.78  tff(c_819, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_373, c_54, c_371, c_815])).
% 4.17/1.78  tff(c_832, plain, (k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_819, c_10])).
% 4.17/1.78  tff(c_838, plain, (k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_557, c_832])).
% 4.17/1.78  tff(c_845, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_838, c_6])).
% 4.17/1.78  tff(c_851, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_557, c_845])).
% 4.17/1.78  tff(c_863, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_18, c_851])).
% 4.17/1.78  tff(c_871, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_117, c_62, c_54, c_464, c_863])).
% 4.17/1.78  tff(c_918, plain, (![B_139, A_140, C_141]: (k2_relset_1(B_139, A_140, k2_funct_1(C_141))=k2_relat_1(k2_funct_1(C_141)) | k2_relset_1(A_140, B_139, C_141)!=B_139 | ~v2_funct_1(C_141) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_140, B_139))) | ~v1_funct_2(C_141, A_140, B_139) | ~v1_funct_1(C_141))), inference(resolution, [status(thm)], [c_637, c_26])).
% 4.17/1.78  tff(c_924, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_372, c_918])).
% 4.17/1.78  tff(c_928, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_373, c_54, c_371, c_924])).
% 4.17/1.78  tff(c_947, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_871, c_928])).
% 4.17/1.78  tff(c_517, plain, (![A_99]: (k10_relat_1(k2_funct_1('#skF_3'), A_99)=k9_relat_1('#skF_3', A_99))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_62, c_54, c_510])).
% 4.17/1.78  tff(c_987, plain, (![B_145, A_146]: (k10_relat_1(k7_relat_1(k2_funct_1(B_145), A_146), k10_relat_1(B_145, A_146))=k1_relat_1(k7_relat_1(k2_funct_1(B_145), A_146)) | ~v1_relat_1(k7_relat_1(k2_funct_1(B_145), A_146)) | ~v1_relat_1(k2_funct_1(B_145)) | ~v2_funct_1(B_145) | ~v1_funct_1(B_145) | ~v1_relat_1(B_145))), inference(superposition, [status(thm), theory('equality')], [c_18, c_443])).
% 4.17/1.78  tff(c_1008, plain, (![A_99]: (k10_relat_1(k7_relat_1(k2_funct_1(k2_funct_1('#skF_3')), A_99), k9_relat_1('#skF_3', A_99))=k1_relat_1(k7_relat_1(k2_funct_1(k2_funct_1('#skF_3')), A_99)) | ~v1_relat_1(k7_relat_1(k2_funct_1(k2_funct_1('#skF_3')), A_99)) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_517, c_987])).
% 4.17/1.78  tff(c_1026, plain, (![A_99]: (k10_relat_1(k7_relat_1(k2_funct_1(k2_funct_1('#skF_3')), A_99), k9_relat_1('#skF_3', A_99))=k1_relat_1(k7_relat_1(k2_funct_1(k2_funct_1('#skF_3')), A_99)) | ~v1_relat_1(k7_relat_1(k2_funct_1(k2_funct_1('#skF_3')), A_99)) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_557, c_471, c_1008])).
% 4.17/1.78  tff(c_1038, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1026])).
% 4.17/1.78  tff(c_1041, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_1038])).
% 4.17/1.78  tff(c_1045, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_117, c_62, c_54, c_1041])).
% 4.17/1.78  tff(c_1047, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1026])).
% 4.17/1.78  tff(c_14, plain, (![A_11]: (v1_funct_1(k2_funct_1(A_11)) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.17/1.78  tff(c_569, plain, (![A_104, A_105]: (k10_relat_1(k2_funct_1(A_104), A_105)=k9_relat_1(A_104, A_105) | ~v2_funct_1(A_104) | ~v1_funct_1(A_104) | ~v1_relat_1(A_104))), inference(resolution, [status(thm)], [c_14, c_508])).
% 4.17/1.78  tff(c_602, plain, (![A_106]: (k9_relat_1(A_106, k2_relat_1(k2_funct_1(A_106)))=k1_relat_1(k2_funct_1(A_106)) | ~v1_relat_1(k2_funct_1(A_106)) | ~v2_funct_1(A_106) | ~v1_funct_1(A_106) | ~v1_relat_1(A_106))), inference(superposition, [status(thm), theory('equality')], [c_569, c_8])).
% 4.17/1.78  tff(c_1029, plain, (![A_147]: (k9_relat_1(k2_funct_1(A_147), k2_relat_1(A_147))=k1_relat_1(k2_funct_1(k2_funct_1(A_147))) | ~v1_relat_1(k2_funct_1(k2_funct_1(A_147))) | ~v2_funct_1(k2_funct_1(A_147)) | ~v1_funct_1(k2_funct_1(A_147)) | ~v1_relat_1(k2_funct_1(A_147)) | ~v2_funct_1(A_147) | ~v1_funct_1(A_147) | ~v1_relat_1(A_147))), inference(superposition, [status(thm), theory('equality')], [c_20, c_602])).
% 4.17/1.78  tff(c_1048, plain, (![A_148]: (k9_relat_1(k2_funct_1(A_148), k2_relat_1(A_148))=k1_relat_1(k2_funct_1(k2_funct_1(A_148))) | ~v2_funct_1(A_148) | ~v1_funct_1(A_148) | ~v1_relat_1(A_148) | ~v2_funct_1(k2_funct_1(A_148)) | ~v1_funct_1(k2_funct_1(A_148)) | ~v1_relat_1(k2_funct_1(A_148)))), inference(resolution, [status(thm)], [c_16, c_1029])).
% 4.17/1.78  tff(c_930, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_871, c_851])).
% 4.17/1.78  tff(c_1054, plain, (k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1048, c_930])).
% 4.17/1.78  tff(c_1082, plain, (k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_557, c_471, c_1047, c_117, c_62, c_54, c_1054])).
% 4.17/1.78  tff(c_32, plain, (![B_26]: (v1_partfun1(B_26, k1_relat_1(B_26)) | ~v4_relat_1(B_26, k1_relat_1(B_26)) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.17/1.78  tff(c_1091, plain, (v1_partfun1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v4_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1082, c_32])).
% 4.17/1.78  tff(c_1097, plain, (v1_partfun1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3')) | ~v4_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1082, c_1091])).
% 4.17/1.78  tff(c_1114, plain, (~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_1097])).
% 4.17/1.78  tff(c_1117, plain, (~v1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_20, c_1114])).
% 4.17/1.78  tff(c_1123, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_117, c_62, c_54, c_117, c_1117])).
% 4.17/1.78  tff(c_1125, plain, (v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_1097])).
% 4.17/1.78  tff(c_285, plain, (v4_relat_1('#skF_3', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_281, c_134])).
% 4.17/1.78  tff(c_1124, plain, (~v4_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3')) | v1_partfun1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1097])).
% 4.17/1.78  tff(c_1159, plain, (~v4_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1124])).
% 4.17/1.78  tff(c_1162, plain, (~v4_relat_1('#skF_3', k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_20, c_1159])).
% 4.17/1.78  tff(c_1165, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_117, c_62, c_54, c_285, c_1162])).
% 4.17/1.78  tff(c_1167, plain, (v4_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1124])).
% 4.17/1.78  tff(c_1178, plain, (k7_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_1167, c_10])).
% 4.17/1.78  tff(c_1187, plain, (k7_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1125, c_1178])).
% 4.17/1.78  tff(c_1206, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_20, c_1187])).
% 4.17/1.78  tff(c_1218, plain, (k2_funct_1(k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_117, c_62, c_54, c_284, c_1206])).
% 4.17/1.78  tff(c_50, plain, (![A_36, B_37, C_38]: (k2_tops_2(A_36, B_37, C_38)=k2_funct_1(C_38) | ~v2_funct_1(C_38) | k2_relset_1(A_36, B_37, C_38)!=B_37 | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))) | ~v1_funct_2(C_38, A_36, B_37) | ~v1_funct_1(C_38))), inference(cnfTransformation, [status(thm)], [f_164])).
% 4.17/1.78  tff(c_1803, plain, (![B_184, A_185, C_186]: (k2_tops_2(B_184, A_185, k2_funct_1(C_186))=k2_funct_1(k2_funct_1(C_186)) | ~v2_funct_1(k2_funct_1(C_186)) | k2_relset_1(B_184, A_185, k2_funct_1(C_186))!=A_185 | ~v1_funct_2(k2_funct_1(C_186), B_184, A_185) | ~v1_funct_1(k2_funct_1(C_186)) | k2_relset_1(A_185, B_184, C_186)!=B_184 | ~v2_funct_1(C_186) | ~m1_subset_1(C_186, k1_zfmisc_1(k2_zfmisc_1(A_185, B_184))) | ~v1_funct_2(C_186, A_185, B_184) | ~v1_funct_1(C_186))), inference(resolution, [status(thm)], [c_637, c_50])).
% 4.17/1.78  tff(c_1812, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_372, c_1803])).
% 4.17/1.78  tff(c_1819, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_373, c_54, c_371, c_471, c_495, c_947, c_1047, c_1218, c_1812])).
% 4.17/1.78  tff(c_536, plain, (![A_101, B_102, C_103]: (k2_tops_2(A_101, B_102, C_103)=k2_funct_1(C_103) | ~v2_funct_1(C_103) | k2_relset_1(A_101, B_102, C_103)!=B_102 | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))) | ~v1_funct_2(C_103, A_101, B_102) | ~v1_funct_1(C_103))), inference(cnfTransformation, [status(thm)], [f_164])).
% 4.17/1.78  tff(c_539, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_372, c_536])).
% 4.17/1.78  tff(c_542, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_373, c_371, c_54, c_539])).
% 4.17/1.78  tff(c_52, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.17/1.78  tff(c_123, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_78, c_78, c_77, c_77, c_77, c_52])).
% 4.17/1.78  tff(c_286, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_281, c_281, c_281, c_123])).
% 4.17/1.78  tff(c_407, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_366, c_366, c_366, c_286])).
% 4.17/1.78  tff(c_543, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_542, c_407])).
% 4.17/1.78  tff(c_1820, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1819, c_543])).
% 4.17/1.78  tff(c_1823, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_434, c_1820])).
% 4.17/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.17/1.78  
% 4.17/1.78  Inference rules
% 4.17/1.78  ----------------------
% 4.17/1.78  #Ref     : 0
% 4.17/1.78  #Sup     : 374
% 4.17/1.78  #Fact    : 0
% 4.17/1.78  #Define  : 0
% 4.17/1.78  #Split   : 8
% 4.17/1.78  #Chain   : 0
% 4.17/1.78  #Close   : 0
% 4.17/1.78  
% 4.17/1.78  Ordering : KBO
% 4.17/1.78  
% 4.17/1.78  Simplification rules
% 4.17/1.78  ----------------------
% 4.17/1.78  #Subsume      : 19
% 4.17/1.78  #Demod        : 997
% 4.17/1.78  #Tautology    : 237
% 4.17/1.78  #SimpNegUnit  : 8
% 4.17/1.78  #BackRed      : 42
% 4.17/1.78  
% 4.17/1.78  #Partial instantiations: 0
% 4.17/1.78  #Strategies tried      : 1
% 4.17/1.78  
% 4.17/1.78  Timing (in seconds)
% 4.17/1.78  ----------------------
% 4.62/1.78  Preprocessing        : 0.34
% 4.62/1.78  Parsing              : 0.18
% 4.62/1.78  CNF conversion       : 0.02
% 4.62/1.78  Main loop            : 0.62
% 4.62/1.78  Inferencing          : 0.22
% 4.62/1.78  Reduction            : 0.23
% 4.62/1.78  Demodulation         : 0.17
% 4.62/1.78  BG Simplification    : 0.03
% 4.62/1.78  Subsumption          : 0.09
% 4.62/1.78  Abstraction          : 0.03
% 4.62/1.78  MUC search           : 0.00
% 4.62/1.78  Cooper               : 0.00
% 4.62/1.78  Total                : 1.02
% 4.62/1.78  Index Insertion      : 0.00
% 4.62/1.78  Index Deletion       : 0.00
% 4.62/1.78  Index Matching       : 0.00
% 4.62/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
