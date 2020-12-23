%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:37 EST 2020

% Result     : Theorem 9.07s
% Output     : CNFRefutation 9.42s
% Verified   : 
% Statistics : Number of formulae       :  168 (4834 expanded)
%              Number of leaves         :   44 (1724 expanded)
%              Depth                    :   22
%              Number of atoms          :  386 (14101 expanded)
%              Number of equality atoms :   72 (2948 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k4_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_176,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tops_2)).

tff(f_134,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_142,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_114,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_funct_2(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_130,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(C)
          & k2_relset_1(A,B,C) = B )
       => ( v1_funct_1(k2_funct_1(C))
          & v1_funct_2(k2_funct_1(C),B,A)
          & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_60,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_48,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_154,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_64,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_66,plain,(
    ! [A_40] :
      ( u1_struct_0(A_40) = k2_struct_0(A_40)
      | ~ l1_struct_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_74,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_66])).

tff(c_60,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_73,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_66])).

tff(c_54,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_120,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_73,c_54])).

tff(c_121,plain,(
    ! [B_44,A_45] :
      ( v1_relat_1(B_44)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_45))
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_124,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_120,c_121])).

tff(c_127,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_124])).

tff(c_58,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_50,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_216,plain,(
    ! [A_60,B_61,C_62] :
      ( k2_relset_1(A_60,B_61,C_62) = k2_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_220,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_120,c_216])).

tff(c_52,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_115,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_73,c_52])).

tff(c_221,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_115])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_93,plain,(
    ! [A_42] :
      ( ~ v1_xboole_0(u1_struct_0(A_42))
      | ~ l1_struct_0(A_42)
      | v2_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_99,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_93])).

tff(c_103,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_99])).

tff(c_104,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_103])).

tff(c_230,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_104])).

tff(c_56,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_83,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_73,c_56])).

tff(c_231,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_83])).

tff(c_229,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_120])).

tff(c_273,plain,(
    ! [C_63,A_64,B_65] :
      ( v1_partfun1(C_63,A_64)
      | ~ v1_funct_2(C_63,A_64,B_65)
      | ~ v1_funct_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65)))
      | v1_xboole_0(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_276,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_229,c_273])).

tff(c_279,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_231,c_276])).

tff(c_280,plain,(
    v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_230,c_279])).

tff(c_134,plain,(
    ! [C_49,A_50,B_51] :
      ( v4_relat_1(C_49,A_50)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_138,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_120,c_134])).

tff(c_209,plain,(
    ! [B_58,A_59] :
      ( k1_relat_1(B_58) = A_59
      | ~ v1_partfun1(B_58,A_59)
      | ~ v4_relat_1(B_58,A_59)
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_212,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_138,c_209])).

tff(c_215,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_212])).

tff(c_272,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_215])).

tff(c_282,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_272])).

tff(c_283,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_215])).

tff(c_287,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_231])).

tff(c_285,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_229])).

tff(c_2456,plain,(
    ! [A_158,B_159,C_160,D_161] :
      ( r2_funct_2(A_158,B_159,C_160,C_160)
      | ~ m1_subset_1(D_161,k1_zfmisc_1(k2_zfmisc_1(A_158,B_159)))
      | ~ v1_funct_2(D_161,A_158,B_159)
      | ~ v1_funct_1(D_161)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(A_158,B_159)))
      | ~ v1_funct_2(C_160,A_158,B_159)
      | ~ v1_funct_1(C_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_2460,plain,(
    ! [C_160] :
      ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_160,C_160)
      | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_160,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_160) ) ),
    inference(resolution,[status(thm)],[c_285,c_2456])).

tff(c_2476,plain,(
    ! [C_165] :
      ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_165,C_165)
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_165,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_165) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_287,c_2460])).

tff(c_2481,plain,
    ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_285,c_2476])).

tff(c_2485,plain,(
    r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_287,c_2481])).

tff(c_18,plain,(
    ! [A_9] :
      ( k2_funct_1(k2_funct_1(A_9)) = A_9
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_226,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_220])).

tff(c_286,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_226])).

tff(c_1666,plain,(
    ! [C_127,A_128,B_129] :
      ( v1_funct_1(k2_funct_1(C_127))
      | k2_relset_1(A_128,B_129,C_127) != B_129
      | ~ v2_funct_1(C_127)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129)))
      | ~ v1_funct_2(C_127,A_128,B_129)
      | ~ v1_funct_1(C_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1669,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_285,c_1666])).

tff(c_1672,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_287,c_50,c_286,c_1669])).

tff(c_16,plain,(
    ! [A_8] :
      ( v1_relat_1(k2_funct_1(A_8))
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_142,plain,(
    ! [A_55] :
      ( k4_relat_1(A_55) = k2_funct_1(A_55)
      | ~ v2_funct_1(A_55)
      | ~ v1_funct_1(A_55)
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_148,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_142])).

tff(c_152,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_58,c_148])).

tff(c_8,plain,(
    ! [A_6] :
      ( k1_relat_1(k4_relat_1(A_6)) = k2_relat_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_159,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_8])).

tff(c_165,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_159])).

tff(c_201,plain,(
    ! [B_57] :
      ( v1_partfun1(B_57,k1_relat_1(B_57))
      | ~ v4_relat_1(B_57,k1_relat_1(B_57))
      | ~ v1_relat_1(B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_204,plain,
    ( v1_partfun1(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')))
    | ~ v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_201])).

tff(c_208,plain,
    ( v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_204])).

tff(c_351,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_208])).

tff(c_355,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_351])).

tff(c_359,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_58,c_50,c_355])).

tff(c_361,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_208])).

tff(c_12,plain,(
    ! [A_8] :
      ( v2_funct_1(k2_funct_1(A_8))
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1651,plain,(
    ! [A_126] :
      ( k4_relat_1(k2_funct_1(A_126)) = k2_funct_1(k2_funct_1(A_126))
      | ~ v1_funct_1(k2_funct_1(A_126))
      | ~ v1_relat_1(k2_funct_1(A_126))
      | ~ v2_funct_1(A_126)
      | ~ v1_funct_1(A_126)
      | ~ v1_relat_1(A_126) ) ),
    inference(resolution,[status(thm)],[c_12,c_142])).

tff(c_1654,plain,
    ( k4_relat_1(k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_361,c_1651])).

tff(c_1663,plain,
    ( k4_relat_1(k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_58,c_50,c_1654])).

tff(c_1665,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1663])).

tff(c_1674,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1672,c_1665])).

tff(c_1676,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1663])).

tff(c_1858,plain,(
    ! [C_135,B_136,A_137] :
      ( v1_funct_2(k2_funct_1(C_135),B_136,A_137)
      | k2_relset_1(A_137,B_136,C_135) != B_136
      | ~ v2_funct_1(C_135)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_137,B_136)))
      | ~ v1_funct_2(C_135,A_137,B_136)
      | ~ v1_funct_1(C_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1861,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_285,c_1858])).

tff(c_1864,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_287,c_50,c_286,c_1861])).

tff(c_6,plain,(
    ! [A_6] :
      ( k2_relat_1(k4_relat_1(A_6)) = k1_relat_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_156,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_6])).

tff(c_163,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_156])).

tff(c_2184,plain,(
    ! [C_145,B_146,A_147] :
      ( m1_subset_1(k2_funct_1(C_145),k1_zfmisc_1(k2_zfmisc_1(B_146,A_147)))
      | k2_relset_1(A_147,B_146,C_145) != B_146
      | ~ v2_funct_1(C_145)
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(A_147,B_146)))
      | ~ v1_funct_2(C_145,A_147,B_146)
      | ~ v1_funct_1(C_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_24,plain,(
    ! [A_13,B_14,C_15] :
      ( k2_relset_1(A_13,B_14,C_15) = k2_relat_1(C_15)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2601,plain,(
    ! [B_169,A_170,C_171] :
      ( k2_relset_1(B_169,A_170,k2_funct_1(C_171)) = k2_relat_1(k2_funct_1(C_171))
      | k2_relset_1(A_170,B_169,C_171) != B_169
      | ~ v2_funct_1(C_171)
      | ~ m1_subset_1(C_171,k1_zfmisc_1(k2_zfmisc_1(A_170,B_169)))
      | ~ v1_funct_2(C_171,A_170,B_169)
      | ~ v1_funct_1(C_171) ) ),
    inference(resolution,[status(thm)],[c_2184,c_24])).

tff(c_2607,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_285,c_2601])).

tff(c_2611,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_287,c_50,c_286,c_163,c_2607])).

tff(c_1675,plain,(
    k4_relat_1(k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1663])).

tff(c_1485,plain,(
    ! [C_118,A_119,B_120] :
      ( v1_funct_1(k2_funct_1(C_118))
      | k2_relset_1(A_119,B_120,C_118) != B_120
      | ~ v2_funct_1(C_118)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120)))
      | ~ v1_funct_2(C_118,A_119,B_120)
      | ~ v1_funct_1(C_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1488,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_285,c_1485])).

tff(c_1491,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_287,c_50,c_286,c_1488])).

tff(c_1492,plain,(
    ! [A_121] :
      ( k4_relat_1(k2_funct_1(A_121)) = k2_funct_1(k2_funct_1(A_121))
      | ~ v1_funct_1(k2_funct_1(A_121))
      | ~ v1_relat_1(k2_funct_1(A_121))
      | ~ v2_funct_1(A_121)
      | ~ v1_funct_1(A_121)
      | ~ v1_relat_1(A_121) ) ),
    inference(resolution,[status(thm)],[c_12,c_142])).

tff(c_1495,plain,
    ( k4_relat_1(k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_361,c_1492])).

tff(c_1504,plain,(
    k4_relat_1(k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_58,c_50,c_1491,c_1495])).

tff(c_1456,plain,(
    ! [A_116] :
      ( v1_partfun1(k4_relat_1(A_116),k1_relat_1(k4_relat_1(A_116)))
      | ~ v4_relat_1(k4_relat_1(A_116),k2_relat_1(A_116))
      | ~ v1_relat_1(k4_relat_1(A_116))
      | ~ v1_relat_1(A_116) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_201])).

tff(c_1470,plain,(
    ! [A_117] :
      ( v1_partfun1(k4_relat_1(A_117),k2_relat_1(A_117))
      | ~ v4_relat_1(k4_relat_1(A_117),k2_relat_1(A_117))
      | ~ v1_relat_1(k4_relat_1(A_117))
      | ~ v1_relat_1(A_117)
      | ~ v1_relat_1(A_117) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1456])).

tff(c_1473,plain,
    ( v1_partfun1(k4_relat_1(k2_funct_1('#skF_3')),k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v4_relat_1(k4_relat_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3'))
    | ~ v1_relat_1(k4_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_1470])).

tff(c_1481,plain,
    ( v1_partfun1(k4_relat_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3'))
    | ~ v4_relat_1(k4_relat_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3'))
    | ~ v1_relat_1(k4_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_361,c_361,c_163,c_1473])).

tff(c_1484,plain,(
    ~ v1_relat_1(k4_relat_1(k2_funct_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_1481])).

tff(c_1506,plain,(
    ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1504,c_1484])).

tff(c_1538,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1506])).

tff(c_1544,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_58,c_50,c_127,c_1538])).

tff(c_1546,plain,(
    v1_relat_1(k4_relat_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_1481])).

tff(c_1680,plain,(
    v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1675,c_1546])).

tff(c_149,plain,(
    ! [A_8] :
      ( k4_relat_1(k2_funct_1(A_8)) = k2_funct_1(k2_funct_1(A_8))
      | ~ v1_funct_1(k2_funct_1(A_8))
      | ~ v1_relat_1(k2_funct_1(A_8))
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(resolution,[status(thm)],[c_12,c_142])).

tff(c_1712,plain,
    ( k4_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1680,c_149])).

tff(c_1718,plain,
    ( k4_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_361,c_1676,c_1712])).

tff(c_1791,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1718])).

tff(c_1794,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_1791])).

tff(c_1798,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_58,c_50,c_1794])).

tff(c_1800,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1718])).

tff(c_46,plain,(
    ! [A_31,B_32,C_33] :
      ( k2_tops_2(A_31,B_32,C_33) = k2_funct_1(C_33)
      | ~ v2_funct_1(C_33)
      | k2_relset_1(A_31,B_32,C_33) != B_32
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32)))
      | ~ v1_funct_2(C_33,A_31,B_32)
      | ~ v1_funct_1(C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_3965,plain,(
    ! [B_218,A_219,C_220] :
      ( k2_tops_2(B_218,A_219,k2_funct_1(C_220)) = k2_funct_1(k2_funct_1(C_220))
      | ~ v2_funct_1(k2_funct_1(C_220))
      | k2_relset_1(B_218,A_219,k2_funct_1(C_220)) != A_219
      | ~ v1_funct_2(k2_funct_1(C_220),B_218,A_219)
      | ~ v1_funct_1(k2_funct_1(C_220))
      | k2_relset_1(A_219,B_218,C_220) != B_218
      | ~ v2_funct_1(C_220)
      | ~ m1_subset_1(C_220,k1_zfmisc_1(k2_zfmisc_1(A_219,B_218)))
      | ~ v1_funct_2(C_220,A_219,B_218)
      | ~ v1_funct_1(C_220) ) ),
    inference(resolution,[status(thm)],[c_2184,c_46])).

tff(c_3971,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_285,c_3965])).

tff(c_3975,plain,(
    k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_287,c_50,c_286,c_1676,c_1864,c_2611,c_1800,c_3971])).

tff(c_2051,plain,(
    ! [A_139,B_140,C_141] :
      ( k2_tops_2(A_139,B_140,C_141) = k2_funct_1(C_141)
      | ~ v2_funct_1(C_141)
      | k2_relset_1(A_139,B_140,C_141) != B_140
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140)))
      | ~ v1_funct_2(C_141,A_139,B_140)
      | ~ v1_funct_1(C_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_2054,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_285,c_2051])).

tff(c_2057,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_287,c_286,c_50,c_2054])).

tff(c_48,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_128,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_74,c_74,c_73,c_73,c_73,c_48])).

tff(c_228,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_221,c_221,c_128])).

tff(c_1449,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_283,c_283,c_228])).

tff(c_2058,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2057,c_1449])).

tff(c_3976,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3975,c_2058])).

tff(c_3983,plain,
    ( ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_3976])).

tff(c_3986,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_58,c_50,c_2485,c_3983])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n013.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 09:27:24 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.07/3.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.22/3.32  
% 9.22/3.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.22/3.32  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k4_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 9.22/3.32  
% 9.22/3.32  %Foreground sorts:
% 9.22/3.32  
% 9.22/3.32  
% 9.22/3.32  %Background operators:
% 9.22/3.32  
% 9.22/3.32  
% 9.22/3.32  %Foreground operators:
% 9.22/3.32  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.22/3.32  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 9.22/3.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.22/3.32  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 9.22/3.32  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.22/3.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.22/3.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.22/3.32  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 9.22/3.32  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.22/3.32  tff('#skF_2', type, '#skF_2': $i).
% 9.22/3.32  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 9.22/3.32  tff('#skF_3', type, '#skF_3': $i).
% 9.22/3.32  tff('#skF_1', type, '#skF_1': $i).
% 9.22/3.32  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.22/3.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.22/3.32  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 9.22/3.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.22/3.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.22/3.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.22/3.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.22/3.32  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.22/3.32  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.22/3.32  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 9.22/3.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.22/3.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.22/3.32  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 9.22/3.32  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 9.22/3.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.22/3.32  
% 9.42/3.36  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.42/3.36  tff(f_176, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tops_2)).
% 9.42/3.36  tff(f_134, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 9.42/3.36  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 9.42/3.36  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.42/3.36  tff(f_142, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 9.42/3.36  tff(f_92, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 9.42/3.36  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.42/3.36  tff(f_100, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 9.42/3.36  tff(f_114, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_funct_2(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_funct_2)).
% 9.42/3.36  tff(f_68, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 9.42/3.36  tff(f_130, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 9.42/3.36  tff(f_60, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_funct_1)).
% 9.42/3.36  tff(f_48, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 9.42/3.36  tff(f_40, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 9.42/3.36  tff(f_154, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 9.42/3.36  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.42/3.36  tff(c_64, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_176])).
% 9.42/3.36  tff(c_66, plain, (![A_40]: (u1_struct_0(A_40)=k2_struct_0(A_40) | ~l1_struct_0(A_40))), inference(cnfTransformation, [status(thm)], [f_134])).
% 9.42/3.36  tff(c_74, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_64, c_66])).
% 9.42/3.36  tff(c_60, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_176])).
% 9.42/3.36  tff(c_73, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_60, c_66])).
% 9.42/3.36  tff(c_54, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_176])).
% 9.42/3.36  tff(c_120, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_73, c_54])).
% 9.42/3.36  tff(c_121, plain, (![B_44, A_45]: (v1_relat_1(B_44) | ~m1_subset_1(B_44, k1_zfmisc_1(A_45)) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.42/3.36  tff(c_124, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_120, c_121])).
% 9.42/3.36  tff(c_127, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_124])).
% 9.42/3.36  tff(c_58, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_176])).
% 9.42/3.36  tff(c_50, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_176])).
% 9.42/3.36  tff(c_216, plain, (![A_60, B_61, C_62]: (k2_relset_1(A_60, B_61, C_62)=k2_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.42/3.36  tff(c_220, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_120, c_216])).
% 9.42/3.36  tff(c_52, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_176])).
% 9.42/3.36  tff(c_115, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_73, c_52])).
% 9.42/3.36  tff(c_221, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_220, c_115])).
% 9.42/3.36  tff(c_62, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_176])).
% 9.42/3.36  tff(c_93, plain, (![A_42]: (~v1_xboole_0(u1_struct_0(A_42)) | ~l1_struct_0(A_42) | v2_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_142])).
% 9.42/3.36  tff(c_99, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_73, c_93])).
% 9.42/3.36  tff(c_103, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_99])).
% 9.42/3.36  tff(c_104, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_62, c_103])).
% 9.42/3.36  tff(c_230, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_221, c_104])).
% 9.42/3.36  tff(c_56, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_176])).
% 9.42/3.36  tff(c_83, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_73, c_56])).
% 9.42/3.36  tff(c_231, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_221, c_83])).
% 9.42/3.36  tff(c_229, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_221, c_120])).
% 9.42/3.36  tff(c_273, plain, (![C_63, A_64, B_65]: (v1_partfun1(C_63, A_64) | ~v1_funct_2(C_63, A_64, B_65) | ~v1_funct_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))) | v1_xboole_0(B_65))), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.42/3.36  tff(c_276, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_229, c_273])).
% 9.42/3.36  tff(c_279, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_231, c_276])).
% 9.42/3.36  tff(c_280, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_230, c_279])).
% 9.42/3.36  tff(c_134, plain, (![C_49, A_50, B_51]: (v4_relat_1(C_49, A_50) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.42/3.36  tff(c_138, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_120, c_134])).
% 9.42/3.36  tff(c_209, plain, (![B_58, A_59]: (k1_relat_1(B_58)=A_59 | ~v1_partfun1(B_58, A_59) | ~v4_relat_1(B_58, A_59) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.42/3.36  tff(c_212, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_138, c_209])).
% 9.42/3.36  tff(c_215, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_212])).
% 9.42/3.36  tff(c_272, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_215])).
% 9.42/3.36  tff(c_282, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_280, c_272])).
% 9.42/3.36  tff(c_283, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_215])).
% 9.42/3.36  tff(c_287, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_283, c_231])).
% 9.42/3.36  tff(c_285, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_283, c_229])).
% 9.42/3.36  tff(c_2456, plain, (![A_158, B_159, C_160, D_161]: (r2_funct_2(A_158, B_159, C_160, C_160) | ~m1_subset_1(D_161, k1_zfmisc_1(k2_zfmisc_1(A_158, B_159))) | ~v1_funct_2(D_161, A_158, B_159) | ~v1_funct_1(D_161) | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(A_158, B_159))) | ~v1_funct_2(C_160, A_158, B_159) | ~v1_funct_1(C_160))), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.42/3.36  tff(c_2460, plain, (![C_160]: (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_160, C_160) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_160, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_160))), inference(resolution, [status(thm)], [c_285, c_2456])).
% 9.42/3.36  tff(c_2476, plain, (![C_165]: (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_165, C_165) | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_165, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_165))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_287, c_2460])).
% 9.42/3.36  tff(c_2481, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_285, c_2476])).
% 9.42/3.36  tff(c_2485, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_287, c_2481])).
% 9.42/3.36  tff(c_18, plain, (![A_9]: (k2_funct_1(k2_funct_1(A_9))=A_9 | ~v2_funct_1(A_9) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.42/3.36  tff(c_226, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_221, c_220])).
% 9.42/3.36  tff(c_286, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_283, c_226])).
% 9.42/3.36  tff(c_1666, plain, (![C_127, A_128, B_129]: (v1_funct_1(k2_funct_1(C_127)) | k2_relset_1(A_128, B_129, C_127)!=B_129 | ~v2_funct_1(C_127) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))) | ~v1_funct_2(C_127, A_128, B_129) | ~v1_funct_1(C_127))), inference(cnfTransformation, [status(thm)], [f_130])).
% 9.42/3.36  tff(c_1669, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_285, c_1666])).
% 9.42/3.36  tff(c_1672, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_287, c_50, c_286, c_1669])).
% 9.42/3.36  tff(c_16, plain, (![A_8]: (v1_relat_1(k2_funct_1(A_8)) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.42/3.36  tff(c_142, plain, (![A_55]: (k4_relat_1(A_55)=k2_funct_1(A_55) | ~v2_funct_1(A_55) | ~v1_funct_1(A_55) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.42/3.36  tff(c_148, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_142])).
% 9.42/3.36  tff(c_152, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_58, c_148])).
% 9.42/3.36  tff(c_8, plain, (![A_6]: (k1_relat_1(k4_relat_1(A_6))=k2_relat_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.42/3.36  tff(c_159, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_152, c_8])).
% 9.42/3.36  tff(c_165, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_159])).
% 9.42/3.36  tff(c_201, plain, (![B_57]: (v1_partfun1(B_57, k1_relat_1(B_57)) | ~v4_relat_1(B_57, k1_relat_1(B_57)) | ~v1_relat_1(B_57))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.42/3.36  tff(c_204, plain, (v1_partfun1(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3'))) | ~v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_165, c_201])).
% 9.42/3.36  tff(c_208, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_204])).
% 9.42/3.36  tff(c_351, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_208])).
% 9.42/3.36  tff(c_355, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_16, c_351])).
% 9.42/3.36  tff(c_359, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_127, c_58, c_50, c_355])).
% 9.42/3.36  tff(c_361, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_208])).
% 9.42/3.36  tff(c_12, plain, (![A_8]: (v2_funct_1(k2_funct_1(A_8)) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.42/3.36  tff(c_1651, plain, (![A_126]: (k4_relat_1(k2_funct_1(A_126))=k2_funct_1(k2_funct_1(A_126)) | ~v1_funct_1(k2_funct_1(A_126)) | ~v1_relat_1(k2_funct_1(A_126)) | ~v2_funct_1(A_126) | ~v1_funct_1(A_126) | ~v1_relat_1(A_126))), inference(resolution, [status(thm)], [c_12, c_142])).
% 9.42/3.36  tff(c_1654, plain, (k4_relat_1(k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_361, c_1651])).
% 9.42/3.36  tff(c_1663, plain, (k4_relat_1(k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_58, c_50, c_1654])).
% 9.42/3.36  tff(c_1665, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1663])).
% 9.42/3.36  tff(c_1674, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1672, c_1665])).
% 9.42/3.36  tff(c_1676, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1663])).
% 9.42/3.36  tff(c_1858, plain, (![C_135, B_136, A_137]: (v1_funct_2(k2_funct_1(C_135), B_136, A_137) | k2_relset_1(A_137, B_136, C_135)!=B_136 | ~v2_funct_1(C_135) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_137, B_136))) | ~v1_funct_2(C_135, A_137, B_136) | ~v1_funct_1(C_135))), inference(cnfTransformation, [status(thm)], [f_130])).
% 9.42/3.36  tff(c_1861, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_285, c_1858])).
% 9.42/3.36  tff(c_1864, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_287, c_50, c_286, c_1861])).
% 9.42/3.36  tff(c_6, plain, (![A_6]: (k2_relat_1(k4_relat_1(A_6))=k1_relat_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.42/3.36  tff(c_156, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_152, c_6])).
% 9.42/3.36  tff(c_163, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_156])).
% 9.42/3.36  tff(c_2184, plain, (![C_145, B_146, A_147]: (m1_subset_1(k2_funct_1(C_145), k1_zfmisc_1(k2_zfmisc_1(B_146, A_147))) | k2_relset_1(A_147, B_146, C_145)!=B_146 | ~v2_funct_1(C_145) | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(A_147, B_146))) | ~v1_funct_2(C_145, A_147, B_146) | ~v1_funct_1(C_145))), inference(cnfTransformation, [status(thm)], [f_130])).
% 9.42/3.36  tff(c_24, plain, (![A_13, B_14, C_15]: (k2_relset_1(A_13, B_14, C_15)=k2_relat_1(C_15) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.42/3.36  tff(c_2601, plain, (![B_169, A_170, C_171]: (k2_relset_1(B_169, A_170, k2_funct_1(C_171))=k2_relat_1(k2_funct_1(C_171)) | k2_relset_1(A_170, B_169, C_171)!=B_169 | ~v2_funct_1(C_171) | ~m1_subset_1(C_171, k1_zfmisc_1(k2_zfmisc_1(A_170, B_169))) | ~v1_funct_2(C_171, A_170, B_169) | ~v1_funct_1(C_171))), inference(resolution, [status(thm)], [c_2184, c_24])).
% 9.42/3.36  tff(c_2607, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_285, c_2601])).
% 9.42/3.36  tff(c_2611, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_287, c_50, c_286, c_163, c_2607])).
% 9.42/3.36  tff(c_1675, plain, (k4_relat_1(k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1663])).
% 9.42/3.36  tff(c_1485, plain, (![C_118, A_119, B_120]: (v1_funct_1(k2_funct_1(C_118)) | k2_relset_1(A_119, B_120, C_118)!=B_120 | ~v2_funct_1(C_118) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))) | ~v1_funct_2(C_118, A_119, B_120) | ~v1_funct_1(C_118))), inference(cnfTransformation, [status(thm)], [f_130])).
% 9.42/3.36  tff(c_1488, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_285, c_1485])).
% 9.42/3.36  tff(c_1491, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_287, c_50, c_286, c_1488])).
% 9.42/3.36  tff(c_1492, plain, (![A_121]: (k4_relat_1(k2_funct_1(A_121))=k2_funct_1(k2_funct_1(A_121)) | ~v1_funct_1(k2_funct_1(A_121)) | ~v1_relat_1(k2_funct_1(A_121)) | ~v2_funct_1(A_121) | ~v1_funct_1(A_121) | ~v1_relat_1(A_121))), inference(resolution, [status(thm)], [c_12, c_142])).
% 9.42/3.36  tff(c_1495, plain, (k4_relat_1(k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_361, c_1492])).
% 9.42/3.36  tff(c_1504, plain, (k4_relat_1(k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_58, c_50, c_1491, c_1495])).
% 9.42/3.36  tff(c_1456, plain, (![A_116]: (v1_partfun1(k4_relat_1(A_116), k1_relat_1(k4_relat_1(A_116))) | ~v4_relat_1(k4_relat_1(A_116), k2_relat_1(A_116)) | ~v1_relat_1(k4_relat_1(A_116)) | ~v1_relat_1(A_116))), inference(superposition, [status(thm), theory('equality')], [c_8, c_201])).
% 9.42/3.36  tff(c_1470, plain, (![A_117]: (v1_partfun1(k4_relat_1(A_117), k2_relat_1(A_117)) | ~v4_relat_1(k4_relat_1(A_117), k2_relat_1(A_117)) | ~v1_relat_1(k4_relat_1(A_117)) | ~v1_relat_1(A_117) | ~v1_relat_1(A_117))), inference(superposition, [status(thm), theory('equality')], [c_8, c_1456])).
% 9.42/3.36  tff(c_1473, plain, (v1_partfun1(k4_relat_1(k2_funct_1('#skF_3')), k2_relat_1(k2_funct_1('#skF_3'))) | ~v4_relat_1(k4_relat_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3')) | ~v1_relat_1(k4_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_163, c_1470])).
% 9.42/3.36  tff(c_1481, plain, (v1_partfun1(k4_relat_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3')) | ~v4_relat_1(k4_relat_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3')) | ~v1_relat_1(k4_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_361, c_361, c_163, c_1473])).
% 9.42/3.36  tff(c_1484, plain, (~v1_relat_1(k4_relat_1(k2_funct_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_1481])).
% 9.42/3.36  tff(c_1506, plain, (~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1504, c_1484])).
% 9.42/3.36  tff(c_1538, plain, (~v1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_18, c_1506])).
% 9.42/3.36  tff(c_1544, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_127, c_58, c_50, c_127, c_1538])).
% 9.42/3.36  tff(c_1546, plain, (v1_relat_1(k4_relat_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_1481])).
% 9.42/3.36  tff(c_1680, plain, (v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1675, c_1546])).
% 9.42/3.36  tff(c_149, plain, (![A_8]: (k4_relat_1(k2_funct_1(A_8))=k2_funct_1(k2_funct_1(A_8)) | ~v1_funct_1(k2_funct_1(A_8)) | ~v1_relat_1(k2_funct_1(A_8)) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(resolution, [status(thm)], [c_12, c_142])).
% 9.42/3.36  tff(c_1712, plain, (k4_relat_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1680, c_149])).
% 9.42/3.36  tff(c_1718, plain, (k4_relat_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_361, c_1676, c_1712])).
% 9.42/3.36  tff(c_1791, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1718])).
% 9.42/3.36  tff(c_1794, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_1791])).
% 9.42/3.36  tff(c_1798, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_127, c_58, c_50, c_1794])).
% 9.42/3.36  tff(c_1800, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1718])).
% 9.42/3.36  tff(c_46, plain, (![A_31, B_32, C_33]: (k2_tops_2(A_31, B_32, C_33)=k2_funct_1(C_33) | ~v2_funct_1(C_33) | k2_relset_1(A_31, B_32, C_33)!=B_32 | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))) | ~v1_funct_2(C_33, A_31, B_32) | ~v1_funct_1(C_33))), inference(cnfTransformation, [status(thm)], [f_154])).
% 9.42/3.36  tff(c_3965, plain, (![B_218, A_219, C_220]: (k2_tops_2(B_218, A_219, k2_funct_1(C_220))=k2_funct_1(k2_funct_1(C_220)) | ~v2_funct_1(k2_funct_1(C_220)) | k2_relset_1(B_218, A_219, k2_funct_1(C_220))!=A_219 | ~v1_funct_2(k2_funct_1(C_220), B_218, A_219) | ~v1_funct_1(k2_funct_1(C_220)) | k2_relset_1(A_219, B_218, C_220)!=B_218 | ~v2_funct_1(C_220) | ~m1_subset_1(C_220, k1_zfmisc_1(k2_zfmisc_1(A_219, B_218))) | ~v1_funct_2(C_220, A_219, B_218) | ~v1_funct_1(C_220))), inference(resolution, [status(thm)], [c_2184, c_46])).
% 9.42/3.36  tff(c_3971, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_285, c_3965])).
% 9.42/3.36  tff(c_3975, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_287, c_50, c_286, c_1676, c_1864, c_2611, c_1800, c_3971])).
% 9.42/3.36  tff(c_2051, plain, (![A_139, B_140, C_141]: (k2_tops_2(A_139, B_140, C_141)=k2_funct_1(C_141) | ~v2_funct_1(C_141) | k2_relset_1(A_139, B_140, C_141)!=B_140 | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))) | ~v1_funct_2(C_141, A_139, B_140) | ~v1_funct_1(C_141))), inference(cnfTransformation, [status(thm)], [f_154])).
% 9.42/3.36  tff(c_2054, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_285, c_2051])).
% 9.42/3.36  tff(c_2057, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_287, c_286, c_50, c_2054])).
% 9.42/3.36  tff(c_48, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_176])).
% 9.42/3.36  tff(c_128, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_74, c_74, c_73, c_73, c_73, c_48])).
% 9.42/3.36  tff(c_228, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_221, c_221, c_221, c_128])).
% 9.42/3.36  tff(c_1449, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_283, c_283, c_283, c_228])).
% 9.42/3.36  tff(c_2058, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2057, c_1449])).
% 9.42/3.36  tff(c_3976, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3975, c_2058])).
% 9.42/3.36  tff(c_3983, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_18, c_3976])).
% 9.42/3.36  tff(c_3986, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_127, c_58, c_50, c_2485, c_3983])).
% 9.42/3.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.42/3.36  
% 9.42/3.36  Inference rules
% 9.42/3.36  ----------------------
% 9.42/3.36  #Ref     : 0
% 9.42/3.36  #Sup     : 910
% 9.42/3.36  #Fact    : 0
% 9.42/3.36  #Define  : 0
% 9.42/3.36  #Split   : 14
% 9.42/3.36  #Chain   : 0
% 9.42/3.36  #Close   : 0
% 9.42/3.36  
% 9.42/3.36  Ordering : KBO
% 9.42/3.36  
% 9.42/3.36  Simplification rules
% 9.42/3.36  ----------------------
% 9.42/3.36  #Subsume      : 77
% 9.42/3.36  #Demod        : 2540
% 9.42/3.36  #Tautology    : 413
% 9.42/3.36  #SimpNegUnit  : 6
% 9.42/3.36  #BackRed      : 34
% 9.42/3.36  
% 9.42/3.36  #Partial instantiations: 0
% 9.42/3.36  #Strategies tried      : 1
% 9.42/3.36  
% 9.42/3.36  Timing (in seconds)
% 9.42/3.36  ----------------------
% 9.42/3.37  Preprocessing        : 0.58
% 9.42/3.37  Parsing              : 0.30
% 9.42/3.37  CNF conversion       : 0.04
% 9.42/3.37  Main loop            : 1.85
% 9.42/3.37  Inferencing          : 0.60
% 9.42/3.37  Reduction            : 0.68
% 9.42/3.37  Demodulation         : 0.52
% 9.42/3.37  BG Simplification    : 0.08
% 9.42/3.37  Subsumption          : 0.34
% 9.42/3.37  Abstraction          : 0.08
% 9.42/3.37  MUC search           : 0.00
% 9.42/3.37  Cooper               : 0.00
% 9.42/3.37  Total                : 2.51
% 9.42/3.37  Index Insertion      : 0.00
% 9.42/3.37  Index Deletion       : 0.00
% 9.42/3.37  Index Matching       : 0.00
% 9.42/3.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
