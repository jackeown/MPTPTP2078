%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:16 EST 2020

% Result     : Theorem 4.09s
% Output     : CNFRefutation 4.56s
% Verified   : 
% Statistics : Number of formulae       :  206 (13950 expanded)
%              Number of leaves         :   44 (4875 expanded)
%              Depth                    :   22
%              Number of atoms          :  495 (42836 expanded)
%              Number of equality atoms :  126 (13936 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_171,negated_conjecture,(
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
                 => ( k1_relset_1(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) = k2_struct_0(B)
                    & k2_relset_1(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) = k2_struct_0(A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).

tff(f_127,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_135,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_107,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_123,axiom,(
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

tff(f_147,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_49,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_29,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_67,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(c_62,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_64,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_68,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_87,plain,(
    ! [A_38] :
      ( u1_struct_0(A_38) = k2_struct_0(A_38)
      | ~ l1_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_95,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_87])).

tff(c_94,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_87])).

tff(c_58,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_115,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_94,c_58])).

tff(c_813,plain,(
    ! [A_130,B_131,C_132] :
      ( k2_relset_1(A_130,B_131,C_132) = k2_relat_1(C_132)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_817,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_115,c_813])).

tff(c_56,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_110,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_94,c_56])).

tff(c_818,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_817,c_110])).

tff(c_48,plain,(
    ! [A_28] :
      ( ~ v1_xboole_0(k2_struct_0(A_28))
      | ~ l1_struct_0(A_28)
      | v2_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_833,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_818,c_48])).

tff(c_837,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_833])).

tff(c_838,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_837])).

tff(c_22,plain,(
    ! [C_8,A_6,B_7] :
      ( v1_relat_1(C_8)
      | ~ m1_subset_1(C_8,k1_zfmisc_1(k2_zfmisc_1(A_6,B_7))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_119,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_115,c_22])).

tff(c_755,plain,(
    ! [C_119,A_120,B_121] :
      ( v4_relat_1(C_119,A_120)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_759,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_115,c_755])).

tff(c_795,plain,(
    ! [B_124,A_125] :
      ( k1_relat_1(B_124) = A_125
      | ~ v1_partfun1(B_124,A_125)
      | ~ v4_relat_1(B_124,A_125)
      | ~ v1_relat_1(B_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_798,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_759,c_795])).

tff(c_801,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_798])).

tff(c_802,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_801])).

tff(c_60,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_100,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_60])).

tff(c_101,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_100])).

tff(c_828,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_818,c_101])).

tff(c_827,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_818,c_115])).

tff(c_906,plain,(
    ! [C_135,A_136,B_137] :
      ( v1_partfun1(C_135,A_136)
      | ~ v1_funct_2(C_135,A_136,B_137)
      | ~ v1_funct_1(C_135)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137)))
      | v1_xboole_0(B_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_909,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_827,c_906])).

tff(c_912,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_828,c_909])).

tff(c_914,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_838,c_802,c_912])).

tff(c_915,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_801])).

tff(c_919,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_915,c_115])).

tff(c_980,plain,(
    ! [A_142,B_143,C_144] :
      ( k2_relset_1(A_142,B_143,C_144) = k2_relat_1(C_144)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(A_142,B_143))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_984,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_919,c_980])).

tff(c_920,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_915,c_110])).

tff(c_985,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_984,c_920])).

tff(c_921,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_915,c_101])).

tff(c_992,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_985,c_921])).

tff(c_54,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_990,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_985,c_984])).

tff(c_993,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_985,c_919])).

tff(c_1245,plain,(
    ! [C_164,B_165,A_166] :
      ( m1_subset_1(k2_funct_1(C_164),k1_zfmisc_1(k2_zfmisc_1(B_165,A_166)))
      | k2_relset_1(A_166,B_165,C_164) != B_165
      | ~ v2_funct_1(C_164)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(A_166,B_165)))
      | ~ v1_funct_2(C_164,A_166,B_165)
      | ~ v1_funct_1(C_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_30,plain,(
    ! [A_15,B_16,C_17] :
      ( k2_relset_1(A_15,B_16,C_17) = k2_relat_1(C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1438,plain,(
    ! [B_183,A_184,C_185] :
      ( k2_relset_1(B_183,A_184,k2_funct_1(C_185)) = k2_relat_1(k2_funct_1(C_185))
      | k2_relset_1(A_184,B_183,C_185) != B_183
      | ~ v2_funct_1(C_185)
      | ~ m1_subset_1(C_185,k1_zfmisc_1(k2_zfmisc_1(A_184,B_183)))
      | ~ v1_funct_2(C_185,A_184,B_183)
      | ~ v1_funct_1(C_185) ) ),
    inference(resolution,[status(thm)],[c_1245,c_30])).

tff(c_1444,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_993,c_1438])).

tff(c_1448,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_992,c_54,c_990,c_1444])).

tff(c_1185,plain,(
    ! [A_159,B_160,C_161] :
      ( k2_tops_2(A_159,B_160,C_161) = k2_funct_1(C_161)
      | ~ v2_funct_1(C_161)
      | k2_relset_1(A_159,B_160,C_161) != B_160
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(A_159,B_160)))
      | ~ v1_funct_2(C_161,A_159,B_160)
      | ~ v1_funct_1(C_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_1188,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_993,c_1185])).

tff(c_1191,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_992,c_990,c_54,c_1188])).

tff(c_182,plain,(
    ! [A_60,B_61,C_62] :
      ( k2_relset_1(A_60,B_61,C_62) = k2_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_186,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_115,c_182])).

tff(c_199,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_110])).

tff(c_214,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_48])).

tff(c_218,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_214])).

tff(c_219,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_218])).

tff(c_128,plain,(
    ! [C_49,A_50,B_51] :
      ( v4_relat_1(C_49,A_50)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_132,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_115,c_128])).

tff(c_164,plain,(
    ! [B_54,A_55] :
      ( k1_relat_1(B_54) = A_55
      | ~ v1_partfun1(B_54,A_55)
      | ~ v4_relat_1(B_54,A_55)
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_167,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_132,c_164])).

tff(c_170,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_167])).

tff(c_171,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_170])).

tff(c_209,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_101])).

tff(c_208,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_115])).

tff(c_270,plain,(
    ! [C_65,A_66,B_67] :
      ( v1_partfun1(C_65,A_66)
      | ~ v1_funct_2(C_65,A_66,B_67)
      | ~ v1_funct_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67)))
      | v1_xboole_0(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_273,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_208,c_270])).

tff(c_276,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_209,c_273])).

tff(c_278,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_219,c_171,c_276])).

tff(c_279,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_170])).

tff(c_282,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_115])).

tff(c_328,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_282,c_30])).

tff(c_283,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_110])).

tff(c_340,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_328,c_283])).

tff(c_284,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_101])).

tff(c_348,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_340,c_284])).

tff(c_345,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_340,c_328])).

tff(c_347,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_340,c_282])).

tff(c_613,plain,(
    ! [C_95,B_96,A_97] :
      ( m1_subset_1(k2_funct_1(C_95),k1_zfmisc_1(k2_zfmisc_1(B_96,A_97)))
      | k2_relset_1(A_97,B_96,C_95) != B_96
      | ~ v2_funct_1(C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_97,B_96)))
      | ~ v1_funct_2(C_95,A_97,B_96)
      | ~ v1_funct_1(C_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_28,plain,(
    ! [A_12,B_13,C_14] :
      ( k1_relset_1(A_12,B_13,C_14) = k1_relat_1(C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_708,plain,(
    ! [B_110,A_111,C_112] :
      ( k1_relset_1(B_110,A_111,k2_funct_1(C_112)) = k1_relat_1(k2_funct_1(C_112))
      | k2_relset_1(A_111,B_110,C_112) != B_110
      | ~ v2_funct_1(C_112)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_111,B_110)))
      | ~ v1_funct_2(C_112,A_111,B_110)
      | ~ v1_funct_1(C_112) ) ),
    inference(resolution,[status(thm)],[c_613,c_28])).

tff(c_714,plain,
    ( k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_347,c_708])).

tff(c_718,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_348,c_54,c_345,c_714])).

tff(c_601,plain,(
    ! [A_92,B_93,C_94] :
      ( k2_tops_2(A_92,B_93,C_94) = k2_funct_1(C_94)
      | ~ v2_funct_1(C_94)
      | k2_relset_1(A_92,B_93,C_94) != B_93
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93)))
      | ~ v1_funct_2(C_94,A_92,B_93)
      | ~ v1_funct_1(C_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_604,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_347,c_601])).

tff(c_607,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_348,c_345,c_54,c_604])).

tff(c_52,plain,
    ( k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_120,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_95,c_94,c_94,c_95,c_95,c_94,c_94,c_52])).

tff(c_121,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_120])).

tff(c_339,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_279,c_121])).

tff(c_346,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_340,c_340,c_340,c_339])).

tff(c_608,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_607,c_346])).

tff(c_719,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_718,c_608])).

tff(c_431,plain,(
    ! [C_80,A_81,B_82] :
      ( v1_funct_1(k2_funct_1(C_80))
      | k2_relset_1(A_81,B_82,C_80) != B_82
      | ~ v2_funct_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82)))
      | ~ v1_funct_2(C_80,A_81,B_82)
      | ~ v1_funct_1(C_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_434,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_347,c_431])).

tff(c_437,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_348,c_54,c_345,c_434])).

tff(c_653,plain,(
    ! [C_98,A_99,B_100] :
      ( v1_relat_1(k2_funct_1(C_98))
      | k2_relset_1(A_99,B_100,C_98) != B_100
      | ~ v2_funct_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100)))
      | ~ v1_funct_2(C_98,A_99,B_100)
      | ~ v1_funct_1(C_98) ) ),
    inference(resolution,[status(thm)],[c_613,c_22])).

tff(c_659,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_347,c_653])).

tff(c_663,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_348,c_54,c_345,c_659])).

tff(c_10,plain,(
    ! [A_3] :
      ( v2_funct_1(k2_funct_1(A_3))
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4,plain,(
    ! [A_1] : k2_relat_1(k6_relat_1(A_1)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ! [A_4] :
      ( k5_relat_1(k2_funct_1(A_4),A_4) = k6_relat_1(k2_relat_1(A_4))
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_20,plain,(
    ! [A_5] :
      ( k2_funct_1(k2_funct_1(A_5)) = A_5
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_399,plain,(
    ! [A_75] :
      ( k5_relat_1(A_75,k2_funct_1(A_75)) = k6_relat_1(k1_relat_1(A_75))
      | ~ v2_funct_1(A_75)
      | ~ v1_funct_1(A_75)
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_438,plain,(
    ! [A_83] :
      ( k6_relat_1(k1_relat_1(k2_funct_1(A_83))) = k5_relat_1(k2_funct_1(A_83),A_83)
      | ~ v2_funct_1(k2_funct_1(A_83))
      | ~ v1_funct_1(k2_funct_1(A_83))
      | ~ v1_relat_1(k2_funct_1(A_83))
      | ~ v2_funct_1(A_83)
      | ~ v1_funct_1(A_83)
      | ~ v1_relat_1(A_83) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_399])).

tff(c_538,plain,(
    ! [A_89] :
      ( k2_relat_1(k5_relat_1(k2_funct_1(A_89),A_89)) = k1_relat_1(k2_funct_1(A_89))
      | ~ v2_funct_1(k2_funct_1(A_89))
      | ~ v1_funct_1(k2_funct_1(A_89))
      | ~ v1_relat_1(k2_funct_1(A_89))
      | ~ v2_funct_1(A_89)
      | ~ v1_funct_1(A_89)
      | ~ v1_relat_1(A_89) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_438,c_4])).

tff(c_550,plain,(
    ! [A_4] :
      ( k2_relat_1(k6_relat_1(k2_relat_1(A_4))) = k1_relat_1(k2_funct_1(A_4))
      | ~ v2_funct_1(k2_funct_1(A_4))
      | ~ v1_funct_1(k2_funct_1(A_4))
      | ~ v1_relat_1(k2_funct_1(A_4))
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4)
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_538])).

tff(c_724,plain,(
    ! [A_113] :
      ( k1_relat_1(k2_funct_1(A_113)) = k2_relat_1(A_113)
      | ~ v2_funct_1(k2_funct_1(A_113))
      | ~ v1_funct_1(k2_funct_1(A_113))
      | ~ v1_relat_1(k2_funct_1(A_113))
      | ~ v2_funct_1(A_113)
      | ~ v1_funct_1(A_113)
      | ~ v1_relat_1(A_113)
      | ~ v2_funct_1(A_113)
      | ~ v1_funct_1(A_113)
      | ~ v1_relat_1(A_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_550])).

tff(c_732,plain,(
    ! [A_114] :
      ( k1_relat_1(k2_funct_1(A_114)) = k2_relat_1(A_114)
      | ~ v1_funct_1(k2_funct_1(A_114))
      | ~ v1_relat_1(k2_funct_1(A_114))
      | ~ v2_funct_1(A_114)
      | ~ v1_funct_1(A_114)
      | ~ v1_relat_1(A_114) ) ),
    inference(resolution,[status(thm)],[c_10,c_724])).

tff(c_735,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_663,c_732])).

tff(c_744,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_62,c_54,c_437,c_735])).

tff(c_746,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_719,c_744])).

tff(c_747,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_1067,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_985,c_985,c_915,c_915,c_915,c_747])).

tff(c_1193,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1191,c_1067])).

tff(c_1449,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1448,c_1193])).

tff(c_1285,plain,(
    ! [C_167,A_168,B_169] :
      ( v1_relat_1(k2_funct_1(C_167))
      | k2_relset_1(A_168,B_169,C_167) != B_169
      | ~ v2_funct_1(C_167)
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(A_168,B_169)))
      | ~ v1_funct_2(C_167,A_168,B_169)
      | ~ v1_funct_1(C_167) ) ),
    inference(resolution,[status(thm)],[c_1245,c_22])).

tff(c_1291,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_993,c_1285])).

tff(c_1295,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_992,c_54,c_990,c_1291])).

tff(c_1081,plain,(
    ! [C_150,A_151,B_152] :
      ( v1_funct_1(k2_funct_1(C_150))
      | k2_relset_1(A_151,B_152,C_150) != B_152
      | ~ v2_funct_1(C_150)
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(A_151,B_152)))
      | ~ v1_funct_2(C_150,A_151,B_152)
      | ~ v1_funct_1(C_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1084,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_993,c_1081])).

tff(c_1087,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_992,c_54,c_990,c_1084])).

tff(c_26,plain,(
    ! [C_11,A_9,B_10] :
      ( v4_relat_1(C_11,A_9)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1296,plain,(
    ! [C_170,B_171,A_172] :
      ( v4_relat_1(k2_funct_1(C_170),B_171)
      | k2_relset_1(A_172,B_171,C_170) != B_171
      | ~ v2_funct_1(C_170)
      | ~ m1_subset_1(C_170,k1_zfmisc_1(k2_zfmisc_1(A_172,B_171)))
      | ~ v1_funct_2(C_170,A_172,B_171)
      | ~ v1_funct_1(C_170) ) ),
    inference(resolution,[status(thm)],[c_1245,c_26])).

tff(c_1302,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_993,c_1296])).

tff(c_1306,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_992,c_54,c_990,c_1302])).

tff(c_38,plain,(
    ! [B_23,A_22] :
      ( k1_relat_1(B_23) = A_22
      | ~ v1_partfun1(B_23,A_22)
      | ~ v4_relat_1(B_23,A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1309,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1306,c_38])).

tff(c_1312,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1295,c_1309])).

tff(c_1313,plain,(
    ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1312])).

tff(c_748,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) = k2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_917,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')) = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_915,c_915,c_748])).

tff(c_1068,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_985,c_985,c_985,c_917])).

tff(c_1192,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1191,c_1068])).

tff(c_1348,plain,(
    ! [B_177,A_178,C_179] :
      ( k1_relset_1(B_177,A_178,k2_funct_1(C_179)) = k1_relat_1(k2_funct_1(C_179))
      | k2_relset_1(A_178,B_177,C_179) != B_177
      | ~ v2_funct_1(C_179)
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1(A_178,B_177)))
      | ~ v1_funct_2(C_179,A_178,B_177)
      | ~ v1_funct_1(C_179) ) ),
    inference(resolution,[status(thm)],[c_1245,c_28])).

tff(c_1354,plain,
    ( k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_993,c_1348])).

tff(c_1358,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_992,c_54,c_990,c_1192,c_1354])).

tff(c_36,plain,(
    ! [B_23] :
      ( v1_partfun1(B_23,k1_relat_1(B_23))
      | ~ v4_relat_1(B_23,k1_relat_1(B_23))
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1365,plain,
    ( v1_partfun1(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')))
    | ~ v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1358,c_36])).

tff(c_1371,plain,(
    v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1295,c_1306,c_1358,c_1365])).

tff(c_1373,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1313,c_1371])).

tff(c_1374,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1312])).

tff(c_1055,plain,(
    ! [A_146] :
      ( k5_relat_1(A_146,k2_funct_1(A_146)) = k6_relat_1(k1_relat_1(A_146))
      | ~ v2_funct_1(A_146)
      | ~ v1_funct_1(A_146)
      | ~ v1_relat_1(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1064,plain,(
    ! [A_5] :
      ( k6_relat_1(k1_relat_1(k2_funct_1(A_5))) = k5_relat_1(k2_funct_1(A_5),A_5)
      | ~ v2_funct_1(k2_funct_1(A_5))
      | ~ v1_funct_1(k2_funct_1(A_5))
      | ~ v1_relat_1(k2_funct_1(A_5))
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1055])).

tff(c_1379,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_relat_1(k2_relat_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1374,c_1064])).

tff(c_1386,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_relat_1(k2_relat_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_62,c_54,c_1295,c_1087,c_1379])).

tff(c_1391,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1386])).

tff(c_1394,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_1391])).

tff(c_1398,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_62,c_54,c_1394])).

tff(c_1400,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1386])).

tff(c_18,plain,(
    ! [A_4] :
      ( k5_relat_1(A_4,k2_funct_1(A_4)) = k6_relat_1(k1_relat_1(A_4))
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1041,plain,(
    ! [A_145] :
      ( k5_relat_1(k2_funct_1(A_145),A_145) = k6_relat_1(k2_relat_1(A_145))
      | ~ v2_funct_1(A_145)
      | ~ v1_funct_1(A_145)
      | ~ v1_relat_1(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1088,plain,(
    ! [A_153] :
      ( k6_relat_1(k2_relat_1(k2_funct_1(A_153))) = k5_relat_1(A_153,k2_funct_1(A_153))
      | ~ v2_funct_1(k2_funct_1(A_153))
      | ~ v1_funct_1(k2_funct_1(A_153))
      | ~ v1_relat_1(k2_funct_1(A_153))
      | ~ v2_funct_1(A_153)
      | ~ v1_funct_1(A_153)
      | ~ v1_relat_1(A_153) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1041])).

tff(c_1165,plain,(
    ! [A_158] :
      ( k2_relat_1(k5_relat_1(A_158,k2_funct_1(A_158))) = k2_relat_1(k2_funct_1(A_158))
      | ~ v2_funct_1(k2_funct_1(A_158))
      | ~ v1_funct_1(k2_funct_1(A_158))
      | ~ v1_relat_1(k2_funct_1(A_158))
      | ~ v2_funct_1(A_158)
      | ~ v1_funct_1(A_158)
      | ~ v1_relat_1(A_158) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1088,c_4])).

tff(c_1177,plain,(
    ! [A_4] :
      ( k2_relat_1(k6_relat_1(k1_relat_1(A_4))) = k2_relat_1(k2_funct_1(A_4))
      | ~ v2_funct_1(k2_funct_1(A_4))
      | ~ v1_funct_1(k2_funct_1(A_4))
      | ~ v1_relat_1(k2_funct_1(A_4))
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4)
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1165])).

tff(c_1477,plain,(
    ! [A_187] :
      ( k2_relat_1(k2_funct_1(A_187)) = k1_relat_1(A_187)
      | ~ v2_funct_1(k2_funct_1(A_187))
      | ~ v1_funct_1(k2_funct_1(A_187))
      | ~ v1_relat_1(k2_funct_1(A_187))
      | ~ v2_funct_1(A_187)
      | ~ v1_funct_1(A_187)
      | ~ v1_relat_1(A_187)
      | ~ v2_funct_1(A_187)
      | ~ v1_funct_1(A_187)
      | ~ v1_relat_1(A_187) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1177])).

tff(c_1480,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1400,c_1477])).

tff(c_1489,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_62,c_54,c_1295,c_1087,c_1480])).

tff(c_1491,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1449,c_1489])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:59:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.09/1.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.09/1.76  
% 4.09/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.09/1.76  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 4.09/1.76  
% 4.09/1.76  %Foreground sorts:
% 4.09/1.76  
% 4.09/1.76  
% 4.09/1.76  %Background operators:
% 4.09/1.76  
% 4.09/1.76  
% 4.09/1.76  %Foreground operators:
% 4.09/1.76  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.09/1.76  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.09/1.76  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.09/1.76  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.09/1.76  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.09/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.09/1.76  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.09/1.76  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.09/1.76  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 4.09/1.76  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.09/1.76  tff('#skF_2', type, '#skF_2': $i).
% 4.09/1.76  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.09/1.76  tff('#skF_3', type, '#skF_3': $i).
% 4.09/1.76  tff('#skF_1', type, '#skF_1': $i).
% 4.09/1.76  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.09/1.76  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.09/1.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.09/1.76  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.09/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.09/1.76  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.09/1.76  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.09/1.76  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.09/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.09/1.76  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.09/1.76  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.09/1.76  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.09/1.76  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.09/1.76  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.09/1.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.09/1.76  
% 4.56/1.79  tff(f_171, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_2)).
% 4.56/1.79  tff(f_127, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 4.56/1.79  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.56/1.79  tff(f_135, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_struct_0)).
% 4.56/1.79  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.56/1.79  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.56/1.79  tff(f_107, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 4.56/1.79  tff(f_99, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 4.56/1.79  tff(f_123, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 4.56/1.79  tff(f_147, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 4.56/1.79  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.56/1.79  tff(f_49, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_funct_1)).
% 4.56/1.79  tff(f_29, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 4.56/1.79  tff(f_59, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 4.56/1.79  tff(f_67, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 4.56/1.79  tff(c_62, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_171])).
% 4.56/1.79  tff(c_66, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_171])).
% 4.56/1.79  tff(c_64, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_171])).
% 4.56/1.79  tff(c_68, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_171])).
% 4.56/1.79  tff(c_87, plain, (![A_38]: (u1_struct_0(A_38)=k2_struct_0(A_38) | ~l1_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.56/1.79  tff(c_95, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_68, c_87])).
% 4.56/1.79  tff(c_94, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_64, c_87])).
% 4.56/1.79  tff(c_58, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_171])).
% 4.56/1.79  tff(c_115, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_94, c_58])).
% 4.56/1.79  tff(c_813, plain, (![A_130, B_131, C_132]: (k2_relset_1(A_130, B_131, C_132)=k2_relat_1(C_132) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_130, B_131))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.56/1.79  tff(c_817, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_115, c_813])).
% 4.56/1.79  tff(c_56, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_171])).
% 4.56/1.79  tff(c_110, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_94, c_56])).
% 4.56/1.79  tff(c_818, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_817, c_110])).
% 4.56/1.79  tff(c_48, plain, (![A_28]: (~v1_xboole_0(k2_struct_0(A_28)) | ~l1_struct_0(A_28) | v2_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.56/1.79  tff(c_833, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_818, c_48])).
% 4.56/1.79  tff(c_837, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_833])).
% 4.56/1.79  tff(c_838, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_66, c_837])).
% 4.56/1.79  tff(c_22, plain, (![C_8, A_6, B_7]: (v1_relat_1(C_8) | ~m1_subset_1(C_8, k1_zfmisc_1(k2_zfmisc_1(A_6, B_7))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.56/1.79  tff(c_119, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_115, c_22])).
% 4.56/1.79  tff(c_755, plain, (![C_119, A_120, B_121]: (v4_relat_1(C_119, A_120) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.56/1.79  tff(c_759, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_115, c_755])).
% 4.56/1.79  tff(c_795, plain, (![B_124, A_125]: (k1_relat_1(B_124)=A_125 | ~v1_partfun1(B_124, A_125) | ~v4_relat_1(B_124, A_125) | ~v1_relat_1(B_124))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.56/1.79  tff(c_798, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_759, c_795])).
% 4.56/1.79  tff(c_801, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_798])).
% 4.56/1.79  tff(c_802, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_801])).
% 4.56/1.79  tff(c_60, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_171])).
% 4.56/1.79  tff(c_100, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_60])).
% 4.56/1.79  tff(c_101, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_100])).
% 4.56/1.79  tff(c_828, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_818, c_101])).
% 4.56/1.79  tff(c_827, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_818, c_115])).
% 4.56/1.79  tff(c_906, plain, (![C_135, A_136, B_137]: (v1_partfun1(C_135, A_136) | ~v1_funct_2(C_135, A_136, B_137) | ~v1_funct_1(C_135) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))) | v1_xboole_0(B_137))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.56/1.79  tff(c_909, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_827, c_906])).
% 4.56/1.79  tff(c_912, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_828, c_909])).
% 4.56/1.79  tff(c_914, plain, $false, inference(negUnitSimplification, [status(thm)], [c_838, c_802, c_912])).
% 4.56/1.79  tff(c_915, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_801])).
% 4.56/1.79  tff(c_919, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_915, c_115])).
% 4.56/1.79  tff(c_980, plain, (![A_142, B_143, C_144]: (k2_relset_1(A_142, B_143, C_144)=k2_relat_1(C_144) | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(A_142, B_143))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.56/1.79  tff(c_984, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_919, c_980])).
% 4.56/1.79  tff(c_920, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_915, c_110])).
% 4.56/1.79  tff(c_985, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_984, c_920])).
% 4.56/1.79  tff(c_921, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_915, c_101])).
% 4.56/1.79  tff(c_992, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_985, c_921])).
% 4.56/1.79  tff(c_54, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_171])).
% 4.56/1.79  tff(c_990, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_985, c_984])).
% 4.56/1.79  tff(c_993, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_985, c_919])).
% 4.56/1.79  tff(c_1245, plain, (![C_164, B_165, A_166]: (m1_subset_1(k2_funct_1(C_164), k1_zfmisc_1(k2_zfmisc_1(B_165, A_166))) | k2_relset_1(A_166, B_165, C_164)!=B_165 | ~v2_funct_1(C_164) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(A_166, B_165))) | ~v1_funct_2(C_164, A_166, B_165) | ~v1_funct_1(C_164))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.56/1.79  tff(c_30, plain, (![A_15, B_16, C_17]: (k2_relset_1(A_15, B_16, C_17)=k2_relat_1(C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.56/1.79  tff(c_1438, plain, (![B_183, A_184, C_185]: (k2_relset_1(B_183, A_184, k2_funct_1(C_185))=k2_relat_1(k2_funct_1(C_185)) | k2_relset_1(A_184, B_183, C_185)!=B_183 | ~v2_funct_1(C_185) | ~m1_subset_1(C_185, k1_zfmisc_1(k2_zfmisc_1(A_184, B_183))) | ~v1_funct_2(C_185, A_184, B_183) | ~v1_funct_1(C_185))), inference(resolution, [status(thm)], [c_1245, c_30])).
% 4.56/1.79  tff(c_1444, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_993, c_1438])).
% 4.56/1.79  tff(c_1448, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_992, c_54, c_990, c_1444])).
% 4.56/1.79  tff(c_1185, plain, (![A_159, B_160, C_161]: (k2_tops_2(A_159, B_160, C_161)=k2_funct_1(C_161) | ~v2_funct_1(C_161) | k2_relset_1(A_159, B_160, C_161)!=B_160 | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(A_159, B_160))) | ~v1_funct_2(C_161, A_159, B_160) | ~v1_funct_1(C_161))), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.56/1.79  tff(c_1188, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_993, c_1185])).
% 4.56/1.79  tff(c_1191, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_992, c_990, c_54, c_1188])).
% 4.56/1.79  tff(c_182, plain, (![A_60, B_61, C_62]: (k2_relset_1(A_60, B_61, C_62)=k2_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.56/1.79  tff(c_186, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_115, c_182])).
% 4.56/1.79  tff(c_199, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_186, c_110])).
% 4.56/1.79  tff(c_214, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_199, c_48])).
% 4.56/1.79  tff(c_218, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_214])).
% 4.56/1.79  tff(c_219, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_66, c_218])).
% 4.56/1.79  tff(c_128, plain, (![C_49, A_50, B_51]: (v4_relat_1(C_49, A_50) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.56/1.79  tff(c_132, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_115, c_128])).
% 4.56/1.79  tff(c_164, plain, (![B_54, A_55]: (k1_relat_1(B_54)=A_55 | ~v1_partfun1(B_54, A_55) | ~v4_relat_1(B_54, A_55) | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.56/1.79  tff(c_167, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_132, c_164])).
% 4.56/1.79  tff(c_170, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_167])).
% 4.56/1.79  tff(c_171, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_170])).
% 4.56/1.79  tff(c_209, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_199, c_101])).
% 4.56/1.79  tff(c_208, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_199, c_115])).
% 4.56/1.79  tff(c_270, plain, (![C_65, A_66, B_67]: (v1_partfun1(C_65, A_66) | ~v1_funct_2(C_65, A_66, B_67) | ~v1_funct_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))) | v1_xboole_0(B_67))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.56/1.79  tff(c_273, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_208, c_270])).
% 4.56/1.79  tff(c_276, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_209, c_273])).
% 4.56/1.79  tff(c_278, plain, $false, inference(negUnitSimplification, [status(thm)], [c_219, c_171, c_276])).
% 4.56/1.79  tff(c_279, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_170])).
% 4.56/1.79  tff(c_282, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_279, c_115])).
% 4.56/1.79  tff(c_328, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_282, c_30])).
% 4.56/1.79  tff(c_283, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_279, c_110])).
% 4.56/1.79  tff(c_340, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_328, c_283])).
% 4.56/1.79  tff(c_284, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_279, c_101])).
% 4.56/1.79  tff(c_348, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_340, c_284])).
% 4.56/1.79  tff(c_345, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_340, c_328])).
% 4.56/1.79  tff(c_347, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_340, c_282])).
% 4.56/1.79  tff(c_613, plain, (![C_95, B_96, A_97]: (m1_subset_1(k2_funct_1(C_95), k1_zfmisc_1(k2_zfmisc_1(B_96, A_97))) | k2_relset_1(A_97, B_96, C_95)!=B_96 | ~v2_funct_1(C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_97, B_96))) | ~v1_funct_2(C_95, A_97, B_96) | ~v1_funct_1(C_95))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.56/1.79  tff(c_28, plain, (![A_12, B_13, C_14]: (k1_relset_1(A_12, B_13, C_14)=k1_relat_1(C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.56/1.79  tff(c_708, plain, (![B_110, A_111, C_112]: (k1_relset_1(B_110, A_111, k2_funct_1(C_112))=k1_relat_1(k2_funct_1(C_112)) | k2_relset_1(A_111, B_110, C_112)!=B_110 | ~v2_funct_1(C_112) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_111, B_110))) | ~v1_funct_2(C_112, A_111, B_110) | ~v1_funct_1(C_112))), inference(resolution, [status(thm)], [c_613, c_28])).
% 4.56/1.79  tff(c_714, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_347, c_708])).
% 4.56/1.79  tff(c_718, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_348, c_54, c_345, c_714])).
% 4.56/1.79  tff(c_601, plain, (![A_92, B_93, C_94]: (k2_tops_2(A_92, B_93, C_94)=k2_funct_1(C_94) | ~v2_funct_1(C_94) | k2_relset_1(A_92, B_93, C_94)!=B_93 | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))) | ~v1_funct_2(C_94, A_92, B_93) | ~v1_funct_1(C_94))), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.56/1.79  tff(c_604, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_347, c_601])).
% 4.56/1.79  tff(c_607, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_348, c_345, c_54, c_604])).
% 4.56/1.79  tff(c_52, plain, (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_171])).
% 4.56/1.79  tff(c_120, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_95, c_94, c_94, c_95, c_95, c_94, c_94, c_52])).
% 4.56/1.79  tff(c_121, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_120])).
% 4.56/1.79  tff(c_339, plain, (k1_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_279, c_279, c_121])).
% 4.56/1.79  tff(c_346, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_340, c_340, c_340, c_339])).
% 4.56/1.79  tff(c_608, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_607, c_346])).
% 4.56/1.79  tff(c_719, plain, (k1_relat_1(k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_718, c_608])).
% 4.56/1.79  tff(c_431, plain, (![C_80, A_81, B_82]: (v1_funct_1(k2_funct_1(C_80)) | k2_relset_1(A_81, B_82, C_80)!=B_82 | ~v2_funct_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))) | ~v1_funct_2(C_80, A_81, B_82) | ~v1_funct_1(C_80))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.56/1.79  tff(c_434, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_347, c_431])).
% 4.56/1.79  tff(c_437, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_348, c_54, c_345, c_434])).
% 4.56/1.79  tff(c_653, plain, (![C_98, A_99, B_100]: (v1_relat_1(k2_funct_1(C_98)) | k2_relset_1(A_99, B_100, C_98)!=B_100 | ~v2_funct_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))) | ~v1_funct_2(C_98, A_99, B_100) | ~v1_funct_1(C_98))), inference(resolution, [status(thm)], [c_613, c_22])).
% 4.56/1.79  tff(c_659, plain, (v1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_347, c_653])).
% 4.56/1.79  tff(c_663, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_348, c_54, c_345, c_659])).
% 4.56/1.79  tff(c_10, plain, (![A_3]: (v2_funct_1(k2_funct_1(A_3)) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.56/1.79  tff(c_4, plain, (![A_1]: (k2_relat_1(k6_relat_1(A_1))=A_1)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.56/1.79  tff(c_16, plain, (![A_4]: (k5_relat_1(k2_funct_1(A_4), A_4)=k6_relat_1(k2_relat_1(A_4)) | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.56/1.79  tff(c_20, plain, (![A_5]: (k2_funct_1(k2_funct_1(A_5))=A_5 | ~v2_funct_1(A_5) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.56/1.79  tff(c_399, plain, (![A_75]: (k5_relat_1(A_75, k2_funct_1(A_75))=k6_relat_1(k1_relat_1(A_75)) | ~v2_funct_1(A_75) | ~v1_funct_1(A_75) | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.56/1.79  tff(c_438, plain, (![A_83]: (k6_relat_1(k1_relat_1(k2_funct_1(A_83)))=k5_relat_1(k2_funct_1(A_83), A_83) | ~v2_funct_1(k2_funct_1(A_83)) | ~v1_funct_1(k2_funct_1(A_83)) | ~v1_relat_1(k2_funct_1(A_83)) | ~v2_funct_1(A_83) | ~v1_funct_1(A_83) | ~v1_relat_1(A_83))), inference(superposition, [status(thm), theory('equality')], [c_20, c_399])).
% 4.56/1.79  tff(c_538, plain, (![A_89]: (k2_relat_1(k5_relat_1(k2_funct_1(A_89), A_89))=k1_relat_1(k2_funct_1(A_89)) | ~v2_funct_1(k2_funct_1(A_89)) | ~v1_funct_1(k2_funct_1(A_89)) | ~v1_relat_1(k2_funct_1(A_89)) | ~v2_funct_1(A_89) | ~v1_funct_1(A_89) | ~v1_relat_1(A_89))), inference(superposition, [status(thm), theory('equality')], [c_438, c_4])).
% 4.56/1.79  tff(c_550, plain, (![A_4]: (k2_relat_1(k6_relat_1(k2_relat_1(A_4)))=k1_relat_1(k2_funct_1(A_4)) | ~v2_funct_1(k2_funct_1(A_4)) | ~v1_funct_1(k2_funct_1(A_4)) | ~v1_relat_1(k2_funct_1(A_4)) | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4) | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(superposition, [status(thm), theory('equality')], [c_16, c_538])).
% 4.56/1.79  tff(c_724, plain, (![A_113]: (k1_relat_1(k2_funct_1(A_113))=k2_relat_1(A_113) | ~v2_funct_1(k2_funct_1(A_113)) | ~v1_funct_1(k2_funct_1(A_113)) | ~v1_relat_1(k2_funct_1(A_113)) | ~v2_funct_1(A_113) | ~v1_funct_1(A_113) | ~v1_relat_1(A_113) | ~v2_funct_1(A_113) | ~v1_funct_1(A_113) | ~v1_relat_1(A_113))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_550])).
% 4.56/1.79  tff(c_732, plain, (![A_114]: (k1_relat_1(k2_funct_1(A_114))=k2_relat_1(A_114) | ~v1_funct_1(k2_funct_1(A_114)) | ~v1_relat_1(k2_funct_1(A_114)) | ~v2_funct_1(A_114) | ~v1_funct_1(A_114) | ~v1_relat_1(A_114))), inference(resolution, [status(thm)], [c_10, c_724])).
% 4.56/1.79  tff(c_735, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_663, c_732])).
% 4.56/1.79  tff(c_744, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_119, c_62, c_54, c_437, c_735])).
% 4.56/1.79  tff(c_746, plain, $false, inference(negUnitSimplification, [status(thm)], [c_719, c_744])).
% 4.56/1.79  tff(c_747, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_120])).
% 4.56/1.79  tff(c_1067, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_985, c_985, c_915, c_915, c_915, c_747])).
% 4.56/1.79  tff(c_1193, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1191, c_1067])).
% 4.56/1.79  tff(c_1449, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1448, c_1193])).
% 4.56/1.79  tff(c_1285, plain, (![C_167, A_168, B_169]: (v1_relat_1(k2_funct_1(C_167)) | k2_relset_1(A_168, B_169, C_167)!=B_169 | ~v2_funct_1(C_167) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1(A_168, B_169))) | ~v1_funct_2(C_167, A_168, B_169) | ~v1_funct_1(C_167))), inference(resolution, [status(thm)], [c_1245, c_22])).
% 4.56/1.79  tff(c_1291, plain, (v1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_993, c_1285])).
% 4.56/1.79  tff(c_1295, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_992, c_54, c_990, c_1291])).
% 4.56/1.79  tff(c_1081, plain, (![C_150, A_151, B_152]: (v1_funct_1(k2_funct_1(C_150)) | k2_relset_1(A_151, B_152, C_150)!=B_152 | ~v2_funct_1(C_150) | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(A_151, B_152))) | ~v1_funct_2(C_150, A_151, B_152) | ~v1_funct_1(C_150))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.56/1.79  tff(c_1084, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_993, c_1081])).
% 4.56/1.79  tff(c_1087, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_992, c_54, c_990, c_1084])).
% 4.56/1.79  tff(c_26, plain, (![C_11, A_9, B_10]: (v4_relat_1(C_11, A_9) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.56/1.79  tff(c_1296, plain, (![C_170, B_171, A_172]: (v4_relat_1(k2_funct_1(C_170), B_171) | k2_relset_1(A_172, B_171, C_170)!=B_171 | ~v2_funct_1(C_170) | ~m1_subset_1(C_170, k1_zfmisc_1(k2_zfmisc_1(A_172, B_171))) | ~v1_funct_2(C_170, A_172, B_171) | ~v1_funct_1(C_170))), inference(resolution, [status(thm)], [c_1245, c_26])).
% 4.56/1.79  tff(c_1302, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_993, c_1296])).
% 4.56/1.79  tff(c_1306, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_992, c_54, c_990, c_1302])).
% 4.56/1.79  tff(c_38, plain, (![B_23, A_22]: (k1_relat_1(B_23)=A_22 | ~v1_partfun1(B_23, A_22) | ~v4_relat_1(B_23, A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.56/1.79  tff(c_1309, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1306, c_38])).
% 4.56/1.79  tff(c_1312, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1295, c_1309])).
% 4.56/1.79  tff(c_1313, plain, (~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1312])).
% 4.56/1.79  tff(c_748, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))=k2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_120])).
% 4.56/1.79  tff(c_917, plain, (k1_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3'))=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_915, c_915, c_748])).
% 4.56/1.79  tff(c_1068, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_985, c_985, c_985, c_917])).
% 4.56/1.79  tff(c_1192, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1191, c_1068])).
% 4.56/1.79  tff(c_1348, plain, (![B_177, A_178, C_179]: (k1_relset_1(B_177, A_178, k2_funct_1(C_179))=k1_relat_1(k2_funct_1(C_179)) | k2_relset_1(A_178, B_177, C_179)!=B_177 | ~v2_funct_1(C_179) | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1(A_178, B_177))) | ~v1_funct_2(C_179, A_178, B_177) | ~v1_funct_1(C_179))), inference(resolution, [status(thm)], [c_1245, c_28])).
% 4.56/1.79  tff(c_1354, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_993, c_1348])).
% 4.56/1.79  tff(c_1358, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_992, c_54, c_990, c_1192, c_1354])).
% 4.56/1.79  tff(c_36, plain, (![B_23]: (v1_partfun1(B_23, k1_relat_1(B_23)) | ~v4_relat_1(B_23, k1_relat_1(B_23)) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.56/1.79  tff(c_1365, plain, (v1_partfun1(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3'))) | ~v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1358, c_36])).
% 4.56/1.79  tff(c_1371, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1295, c_1306, c_1358, c_1365])).
% 4.56/1.79  tff(c_1373, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1313, c_1371])).
% 4.56/1.79  tff(c_1374, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_1312])).
% 4.56/1.79  tff(c_1055, plain, (![A_146]: (k5_relat_1(A_146, k2_funct_1(A_146))=k6_relat_1(k1_relat_1(A_146)) | ~v2_funct_1(A_146) | ~v1_funct_1(A_146) | ~v1_relat_1(A_146))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.56/1.79  tff(c_1064, plain, (![A_5]: (k6_relat_1(k1_relat_1(k2_funct_1(A_5)))=k5_relat_1(k2_funct_1(A_5), A_5) | ~v2_funct_1(k2_funct_1(A_5)) | ~v1_funct_1(k2_funct_1(A_5)) | ~v1_relat_1(k2_funct_1(A_5)) | ~v2_funct_1(A_5) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1055])).
% 4.56/1.79  tff(c_1379, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_relat_1(k2_relat_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1374, c_1064])).
% 4.56/1.79  tff(c_1386, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_relat_1(k2_relat_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_62, c_54, c_1295, c_1087, c_1379])).
% 4.56/1.79  tff(c_1391, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1386])).
% 4.56/1.79  tff(c_1394, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_1391])).
% 4.56/1.79  tff(c_1398, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_119, c_62, c_54, c_1394])).
% 4.56/1.79  tff(c_1400, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1386])).
% 4.56/1.79  tff(c_18, plain, (![A_4]: (k5_relat_1(A_4, k2_funct_1(A_4))=k6_relat_1(k1_relat_1(A_4)) | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.56/1.79  tff(c_1041, plain, (![A_145]: (k5_relat_1(k2_funct_1(A_145), A_145)=k6_relat_1(k2_relat_1(A_145)) | ~v2_funct_1(A_145) | ~v1_funct_1(A_145) | ~v1_relat_1(A_145))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.56/1.79  tff(c_1088, plain, (![A_153]: (k6_relat_1(k2_relat_1(k2_funct_1(A_153)))=k5_relat_1(A_153, k2_funct_1(A_153)) | ~v2_funct_1(k2_funct_1(A_153)) | ~v1_funct_1(k2_funct_1(A_153)) | ~v1_relat_1(k2_funct_1(A_153)) | ~v2_funct_1(A_153) | ~v1_funct_1(A_153) | ~v1_relat_1(A_153))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1041])).
% 4.56/1.79  tff(c_1165, plain, (![A_158]: (k2_relat_1(k5_relat_1(A_158, k2_funct_1(A_158)))=k2_relat_1(k2_funct_1(A_158)) | ~v2_funct_1(k2_funct_1(A_158)) | ~v1_funct_1(k2_funct_1(A_158)) | ~v1_relat_1(k2_funct_1(A_158)) | ~v2_funct_1(A_158) | ~v1_funct_1(A_158) | ~v1_relat_1(A_158))), inference(superposition, [status(thm), theory('equality')], [c_1088, c_4])).
% 4.56/1.79  tff(c_1177, plain, (![A_4]: (k2_relat_1(k6_relat_1(k1_relat_1(A_4)))=k2_relat_1(k2_funct_1(A_4)) | ~v2_funct_1(k2_funct_1(A_4)) | ~v1_funct_1(k2_funct_1(A_4)) | ~v1_relat_1(k2_funct_1(A_4)) | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4) | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1165])).
% 4.56/1.79  tff(c_1477, plain, (![A_187]: (k2_relat_1(k2_funct_1(A_187))=k1_relat_1(A_187) | ~v2_funct_1(k2_funct_1(A_187)) | ~v1_funct_1(k2_funct_1(A_187)) | ~v1_relat_1(k2_funct_1(A_187)) | ~v2_funct_1(A_187) | ~v1_funct_1(A_187) | ~v1_relat_1(A_187) | ~v2_funct_1(A_187) | ~v1_funct_1(A_187) | ~v1_relat_1(A_187))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_1177])).
% 4.56/1.79  tff(c_1480, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1400, c_1477])).
% 4.56/1.79  tff(c_1489, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_119, c_62, c_54, c_1295, c_1087, c_1480])).
% 4.56/1.79  tff(c_1491, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1449, c_1489])).
% 4.56/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.56/1.79  
% 4.56/1.79  Inference rules
% 4.56/1.79  ----------------------
% 4.56/1.79  #Ref     : 0
% 4.56/1.79  #Sup     : 345
% 4.56/1.79  #Fact    : 0
% 4.56/1.79  #Define  : 0
% 4.56/1.79  #Split   : 8
% 4.56/1.79  #Chain   : 0
% 4.56/1.79  #Close   : 0
% 4.56/1.79  
% 4.56/1.79  Ordering : KBO
% 4.56/1.79  
% 4.56/1.79  Simplification rules
% 4.56/1.79  ----------------------
% 4.56/1.79  #Subsume      : 3
% 4.56/1.79  #Demod        : 273
% 4.56/1.79  #Tautology    : 201
% 4.56/1.79  #SimpNegUnit  : 11
% 4.56/1.79  #BackRed      : 47
% 4.56/1.79  
% 4.56/1.79  #Partial instantiations: 0
% 4.56/1.79  #Strategies tried      : 1
% 4.56/1.79  
% 4.56/1.79  Timing (in seconds)
% 4.56/1.79  ----------------------
% 4.56/1.80  Preprocessing        : 0.38
% 4.56/1.80  Parsing              : 0.20
% 4.56/1.80  CNF conversion       : 0.03
% 4.56/1.80  Main loop            : 0.53
% 4.56/1.80  Inferencing          : 0.19
% 4.56/1.80  Reduction            : 0.18
% 4.56/1.80  Demodulation         : 0.13
% 4.56/1.80  BG Simplification    : 0.03
% 4.56/1.80  Subsumption          : 0.08
% 4.56/1.80  Abstraction          : 0.03
% 4.56/1.80  MUC search           : 0.00
% 4.56/1.80  Cooper               : 0.00
% 4.56/1.80  Total                : 0.99
% 4.56/1.80  Index Insertion      : 0.00
% 4.56/1.80  Index Deletion       : 0.00
% 4.56/1.80  Index Matching       : 0.00
% 4.56/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
