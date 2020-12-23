%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:15 EST 2020

% Result     : Theorem 4.74s
% Output     : CNFRefutation 4.74s
% Verified   : 
% Statistics : Number of formulae       :  238 (8561 expanded)
%              Number of leaves         :   41 (2993 expanded)
%              Depth                    :   17
%              Number of atoms          :  457 (25948 expanded)
%              Number of equality atoms :  155 (8918 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_159,negated_conjecture,(
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

tff(f_115,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_41,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_123,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_111,axiom,(
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

tff(f_135,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(c_66,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_67,plain,(
    ! [A_33] :
      ( u1_struct_0(A_33) = k2_struct_0(A_33)
      | ~ l1_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_75,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_67])).

tff(c_62,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_74,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_67])).

tff(c_56,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_104,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_74,c_56])).

tff(c_105,plain,(
    ! [C_35,A_36,B_37] :
      ( v1_relat_1(C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_109,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_104,c_105])).

tff(c_60,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_52,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_6,plain,(
    ! [A_2] :
      ( k2_relat_1(k2_funct_1(A_2)) = k1_relat_1(A_2)
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1611,plain,(
    ! [A_244,B_245,C_246] :
      ( k2_relset_1(A_244,B_245,C_246) = k2_relat_1(C_246)
      | ~ m1_subset_1(C_246,k1_zfmisc_1(k2_zfmisc_1(A_244,B_245))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1615,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_104,c_1611])).

tff(c_54,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_85,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_74,c_54])).

tff(c_1616,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1615,c_85])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_91,plain,(
    ! [A_34] :
      ( ~ v1_xboole_0(u1_struct_0(A_34))
      | ~ l1_struct_0(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_97,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_91])).

tff(c_101,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_97])).

tff(c_102,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_101])).

tff(c_1624,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1616,c_102])).

tff(c_1576,plain,(
    ! [C_236,A_237,B_238] :
      ( v4_relat_1(C_236,A_237)
      | ~ m1_subset_1(C_236,k1_zfmisc_1(k2_zfmisc_1(A_237,B_238))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1580,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_104,c_1576])).

tff(c_1594,plain,(
    ! [B_241,A_242] :
      ( k1_relat_1(B_241) = A_242
      | ~ v1_partfun1(B_241,A_242)
      | ~ v4_relat_1(B_241,A_242)
      | ~ v1_relat_1(B_241) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1597,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1580,c_1594])).

tff(c_1600,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_1597])).

tff(c_1610,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1600])).

tff(c_58,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_76,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_58])).

tff(c_90,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_76])).

tff(c_1625,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1616,c_90])).

tff(c_1623,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1616,c_104])).

tff(c_1683,plain,(
    ! [C_257,A_258,B_259] :
      ( v1_partfun1(C_257,A_258)
      | ~ v1_funct_2(C_257,A_258,B_259)
      | ~ v1_funct_1(C_257)
      | ~ m1_subset_1(C_257,k1_zfmisc_1(k2_zfmisc_1(A_258,B_259)))
      | v1_xboole_0(B_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1686,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1623,c_1683])).

tff(c_1689,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1625,c_1686])).

tff(c_1691,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1624,c_1610,c_1689])).

tff(c_1692,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1600])).

tff(c_1695,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1692,c_104])).

tff(c_1747,plain,(
    ! [A_261,B_262,C_263] :
      ( k2_relset_1(A_261,B_262,C_263) = k2_relat_1(C_263)
      | ~ m1_subset_1(C_263,k1_zfmisc_1(k2_zfmisc_1(A_261,B_262))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1751,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1695,c_1747])).

tff(c_1698,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1692,c_85])).

tff(c_1752,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1751,c_1698])).

tff(c_1697,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1692,c_90])).

tff(c_1759,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1752,c_1697])).

tff(c_1757,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1752,c_1751])).

tff(c_1758,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1752,c_1695])).

tff(c_1877,plain,(
    ! [C_290,B_291,A_292] :
      ( m1_subset_1(k2_funct_1(C_290),k1_zfmisc_1(k2_zfmisc_1(B_291,A_292)))
      | k2_relset_1(A_292,B_291,C_290) != B_291
      | ~ v2_funct_1(C_290)
      | ~ m1_subset_1(C_290,k1_zfmisc_1(k2_zfmisc_1(A_292,B_291)))
      | ~ v1_funct_2(C_290,A_292,B_291)
      | ~ v1_funct_1(C_290) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_16,plain,(
    ! [A_9,B_10,C_11] :
      ( k2_relset_1(A_9,B_10,C_11) = k2_relat_1(C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2027,plain,(
    ! [B_302,A_303,C_304] :
      ( k2_relset_1(B_302,A_303,k2_funct_1(C_304)) = k2_relat_1(k2_funct_1(C_304))
      | k2_relset_1(A_303,B_302,C_304) != B_302
      | ~ v2_funct_1(C_304)
      | ~ m1_subset_1(C_304,k1_zfmisc_1(k2_zfmisc_1(A_303,B_302)))
      | ~ v1_funct_2(C_304,A_303,B_302)
      | ~ v1_funct_1(C_304) ) ),
    inference(resolution,[status(thm)],[c_1877,c_16])).

tff(c_2033,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1758,c_2027])).

tff(c_2037,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1759,c_52,c_1757,c_2033])).

tff(c_1856,plain,(
    ! [A_286,B_287,C_288] :
      ( k2_tops_2(A_286,B_287,C_288) = k2_funct_1(C_288)
      | ~ v2_funct_1(C_288)
      | k2_relset_1(A_286,B_287,C_288) != B_287
      | ~ m1_subset_1(C_288,k1_zfmisc_1(k2_zfmisc_1(A_286,B_287)))
      | ~ v1_funct_2(C_288,A_286,B_287)
      | ~ v1_funct_1(C_288) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1859,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1758,c_1856])).

tff(c_1862,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1759,c_1757,c_52,c_1859])).

tff(c_166,plain,(
    ! [A_52,B_53,C_54] :
      ( k2_relset_1(A_52,B_53,C_54) = k2_relat_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_170,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_104,c_166])).

tff(c_171,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_85])).

tff(c_180,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_102])).

tff(c_125,plain,(
    ! [C_40,A_41,B_42] :
      ( v4_relat_1(C_40,A_41)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_129,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_104,c_125])).

tff(c_136,plain,(
    ! [B_47,A_48] :
      ( k1_relat_1(B_47) = A_48
      | ~ v1_partfun1(B_47,A_48)
      | ~ v4_relat_1(B_47,A_48)
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_139,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_129,c_136])).

tff(c_142,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_139])).

tff(c_143,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_142])).

tff(c_181,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_90])).

tff(c_179,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_104])).

tff(c_231,plain,(
    ! [C_64,A_65,B_66] :
      ( v1_partfun1(C_64,A_65)
      | ~ v1_funct_2(C_64,A_65,B_66)
      | ~ v1_funct_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66)))
      | v1_xboole_0(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_234,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_179,c_231])).

tff(c_237,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_181,c_234])).

tff(c_239,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_180,c_143,c_237])).

tff(c_240,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_244,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_104])).

tff(c_317,plain,(
    ! [A_70,B_71,C_72] :
      ( k2_relset_1(A_70,B_71,C_72) = k2_relat_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_321,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_244,c_317])).

tff(c_247,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_85])).

tff(c_322,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_321,c_247])).

tff(c_246,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_90])).

tff(c_330,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_246])).

tff(c_328,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_321])).

tff(c_329,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_244])).

tff(c_421,plain,(
    ! [A_95,B_96,C_97] :
      ( k2_tops_2(A_95,B_96,C_97) = k2_funct_1(C_97)
      | ~ v2_funct_1(C_97)
      | k2_relset_1(A_95,B_96,C_97) != B_96
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96)))
      | ~ v1_funct_2(C_97,A_95,B_96)
      | ~ v1_funct_1(C_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_424,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_329,c_421])).

tff(c_427,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_330,c_328,c_52,c_424])).

tff(c_50,plain,
    ( k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_115,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_75,c_74,c_74,c_75,c_75,c_74,c_74,c_50])).

tff(c_116,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_115])).

tff(c_242,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_240,c_116])).

tff(c_372,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_322,c_322,c_242])).

tff(c_428,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_427,c_372])).

tff(c_110,plain,(
    ! [A_38] :
      ( k1_relat_1(A_38) = k1_xboole_0
      | k2_relat_1(A_38) != k1_xboole_0
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_114,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_109,c_110])).

tff(c_117,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_114])).

tff(c_118,plain,(
    ! [A_39] :
      ( k2_relat_1(A_39) = k1_xboole_0
      | k1_relat_1(A_39) != k1_xboole_0
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_121,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_109,c_118])).

tff(c_124,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_121])).

tff(c_414,plain,(
    ! [C_92,B_93,A_94] :
      ( v1_funct_2(k2_funct_1(C_92),B_93,A_94)
      | k2_relset_1(A_94,B_93,C_92) != B_93
      | ~ v2_funct_1(C_92)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_94,B_93)))
      | ~ v1_funct_2(C_92,A_94,B_93)
      | ~ v1_funct_1(C_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_417,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_329,c_414])).

tff(c_420,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_330,c_52,c_328,c_417])).

tff(c_437,plain,(
    ! [C_99,B_100,A_101] :
      ( m1_subset_1(k2_funct_1(C_99),k1_zfmisc_1(k2_zfmisc_1(B_100,A_101)))
      | k2_relset_1(A_101,B_100,C_99) != B_100
      | ~ v2_funct_1(C_99)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_101,B_100)))
      | ~ v1_funct_2(C_99,A_101,B_100)
      | ~ v1_funct_1(C_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_32,plain,(
    ! [B_17,A_16,C_18] :
      ( k1_xboole_0 = B_17
      | k1_relset_1(A_16,B_17,C_18) = A_16
      | ~ v1_funct_2(C_18,A_16,B_17)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_614,plain,(
    ! [A_118,B_119,C_120] :
      ( k1_xboole_0 = A_118
      | k1_relset_1(B_119,A_118,k2_funct_1(C_120)) = B_119
      | ~ v1_funct_2(k2_funct_1(C_120),B_119,A_118)
      | k2_relset_1(A_118,B_119,C_120) != B_119
      | ~ v2_funct_1(C_120)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119)))
      | ~ v1_funct_2(C_120,A_118,B_119)
      | ~ v1_funct_1(C_120) ) ),
    inference(resolution,[status(thm)],[c_437,c_32])).

tff(c_620,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_329,c_614])).

tff(c_624,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_330,c_52,c_328,c_420,c_620])).

tff(c_626,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_428,c_124,c_624])).

tff(c_628,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_627,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_654,plain,(
    ! [B_128] :
      ( v1_partfun1(B_128,k1_relat_1(B_128))
      | ~ v4_relat_1(B_128,k1_relat_1(B_128))
      | ~ v1_relat_1(B_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_657,plain,
    ( v1_partfun1('#skF_3',k1_relat_1('#skF_3'))
    | ~ v4_relat_1('#skF_3',k1_xboole_0)
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_627,c_654])).

tff(c_659,plain,
    ( v1_partfun1('#skF_3',k1_xboole_0)
    | ~ v4_relat_1('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_627,c_657])).

tff(c_667,plain,(
    ~ v4_relat_1('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_659])).

tff(c_691,plain,(
    ! [A_134,B_135,C_136] :
      ( k2_relset_1(A_134,B_135,C_136) = k2_relat_1(C_136)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_694,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_104,c_691])).

tff(c_696,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_628,c_694])).

tff(c_697,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_696,c_85])).

tff(c_708,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_697,c_90])).

tff(c_706,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_697,c_104])).

tff(c_24,plain,(
    ! [C_18,A_16] :
      ( k1_xboole_0 = C_18
      | ~ v1_funct_2(C_18,A_16,k1_xboole_0)
      | k1_xboole_0 = A_16
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_739,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k1_xboole_0)
    | k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_706,c_24])).

tff(c_755,plain,
    ( k1_xboole_0 = '#skF_3'
    | k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_708,c_739])).

tff(c_756,plain,(
    k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_755])).

tff(c_649,plain,(
    ! [C_125,A_126,B_127] :
      ( v4_relat_1(C_125,A_126)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_126,B_127))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_653,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_104,c_649])).

tff(c_762,plain,(
    v4_relat_1('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_756,c_653])).

tff(c_766,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_667,c_762])).

tff(c_767,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_755])).

tff(c_707,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_697,c_102])).

tff(c_776,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_767,c_707])).

tff(c_660,plain,(
    ! [B_129,A_130] :
      ( k1_relat_1(B_129) = A_130
      | ~ v1_partfun1(B_129,A_130)
      | ~ v4_relat_1(B_129,A_130)
      | ~ v1_relat_1(B_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_663,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_653,c_660])).

tff(c_666,plain,
    ( k2_struct_0('#skF_1') = k1_xboole_0
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_627,c_663])).

tff(c_668,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_666])).

tff(c_772,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_767,c_708])).

tff(c_774,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),'#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_767,c_706])).

tff(c_892,plain,(
    ! [C_156,A_157,B_158] :
      ( v1_partfun1(C_156,A_157)
      | ~ v1_funct_2(C_156,A_157,B_158)
      | ~ v1_funct_1(C_156)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1(A_157,B_158)))
      | v1_xboole_0(B_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_895,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),'#skF_3')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_774,c_892])).

tff(c_898,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_772,c_895])).

tff(c_900,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_776,c_668,c_898])).

tff(c_901,plain,(
    k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_666])).

tff(c_903,plain,(
    v4_relat_1('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_901,c_653])).

tff(c_911,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_667,c_903])).

tff(c_912,plain,(
    v1_partfun1('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_659])).

tff(c_942,plain,(
    ! [A_161,B_162,C_163] :
      ( k2_relset_1(A_161,B_162,C_163) = k2_relat_1(C_163)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(A_161,B_162))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_945,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_104,c_942])).

tff(c_947,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_628,c_945])).

tff(c_948,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_947,c_85])).

tff(c_958,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_948,c_90])).

tff(c_956,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_948,c_104])).

tff(c_999,plain,(
    ! [C_165,A_166] :
      ( k1_xboole_0 = C_165
      | ~ v1_funct_2(C_165,A_166,k1_xboole_0)
      | k1_xboole_0 = A_166
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(A_166,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1002,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k1_xboole_0)
    | k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_956,c_999])).

tff(c_1005,plain,
    ( k1_xboole_0 = '#skF_3'
    | k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_958,c_1002])).

tff(c_1006,plain,(
    k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1005])).

tff(c_929,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_666])).

tff(c_1011,plain,(
    ~ v1_partfun1('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1006,c_929])).

tff(c_1017,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_912,c_1011])).

tff(c_1018,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1005])).

tff(c_957,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_948,c_102])).

tff(c_1028,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1018,c_957])).

tff(c_1024,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1018,c_958])).

tff(c_1022,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),'#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1018,c_956])).

tff(c_1134,plain,(
    ! [C_176,A_177,B_178] :
      ( v1_partfun1(C_176,A_177)
      | ~ v1_funct_2(C_176,A_177,B_178)
      | ~ v1_funct_1(C_176)
      | ~ m1_subset_1(C_176,k1_zfmisc_1(k2_zfmisc_1(A_177,B_178)))
      | v1_xboole_0(B_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1137,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),'#skF_3')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1022,c_1134])).

tff(c_1140,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1024,c_1137])).

tff(c_1142,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1028,c_929,c_1140])).

tff(c_1143,plain,(
    k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_666])).

tff(c_1159,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1143,c_104])).

tff(c_1199,plain,(
    ! [A_181,B_182,C_183] :
      ( k2_relset_1(A_181,B_182,C_183) = k2_relat_1(C_183)
      | ~ m1_subset_1(C_183,k1_zfmisc_1(k2_zfmisc_1(A_181,B_182))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1202,plain,(
    k2_relset_1(k1_xboole_0,k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1159,c_1199])).

tff(c_1204,plain,(
    k2_relset_1(k1_xboole_0,k2_struct_0('#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_628,c_1202])).

tff(c_1162,plain,(
    k2_relset_1(k1_xboole_0,k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1143,c_85])).

tff(c_1205,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1204,c_1162])).

tff(c_1161,plain,(
    v1_funct_2('#skF_3',k1_xboole_0,k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1143,c_90])).

tff(c_1213,plain,(
    v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1205,c_1161])).

tff(c_1210,plain,(
    k2_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1205,c_1204])).

tff(c_1212,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1205,c_1159])).

tff(c_1323,plain,(
    ! [A_206,B_207,C_208] :
      ( k2_tops_2(A_206,B_207,C_208) = k2_funct_1(C_208)
      | ~ v2_funct_1(C_208)
      | k2_relset_1(A_206,B_207,C_208) != B_207
      | ~ m1_subset_1(C_208,k1_zfmisc_1(k2_zfmisc_1(A_206,B_207)))
      | ~ v1_funct_2(C_208,A_206,B_207)
      | ~ v1_funct_1(C_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1326,plain,
    ( k2_tops_2(k1_xboole_0,k1_xboole_0,'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') != k1_xboole_0
    | ~ v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1212,c_1323])).

tff(c_1329,plain,(
    k2_tops_2(k1_xboole_0,k1_xboole_0,'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1213,c_1210,c_52,c_1326])).

tff(c_1158,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k1_xboole_0,k2_tops_2(k1_xboole_0,k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1143,c_1143,c_116])).

tff(c_1211,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,k2_tops_2(k1_xboole_0,k1_xboole_0,'#skF_3')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1205,c_1205,c_1205,c_1158])).

tff(c_1330,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1('#skF_3')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1329,c_1211])).

tff(c_1316,plain,(
    ! [C_203,B_204,A_205] :
      ( v1_funct_2(k2_funct_1(C_203),B_204,A_205)
      | k2_relset_1(A_205,B_204,C_203) != B_204
      | ~ v2_funct_1(C_203)
      | ~ m1_subset_1(C_203,k1_zfmisc_1(k2_zfmisc_1(A_205,B_204)))
      | ~ v1_funct_2(C_203,A_205,B_204)
      | ~ v1_funct_1(C_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1319,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k1_xboole_0,k1_xboole_0)
    | k2_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') != k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1212,c_1316])).

tff(c_1322,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1213,c_52,c_1210,c_1319])).

tff(c_1335,plain,(
    ! [C_209,B_210,A_211] :
      ( m1_subset_1(k2_funct_1(C_209),k1_zfmisc_1(k2_zfmisc_1(B_210,A_211)))
      | k2_relset_1(A_211,B_210,C_209) != B_210
      | ~ v2_funct_1(C_209)
      | ~ m1_subset_1(C_209,k1_zfmisc_1(k2_zfmisc_1(A_211,B_210)))
      | ~ v1_funct_2(C_209,A_211,B_210)
      | ~ v1_funct_1(C_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_30,plain,(
    ! [B_17,C_18] :
      ( k1_relset_1(k1_xboole_0,B_17,C_18) = k1_xboole_0
      | ~ v1_funct_2(C_18,k1_xboole_0,B_17)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1548,plain,(
    ! [A_230,C_231] :
      ( k1_relset_1(k1_xboole_0,A_230,k2_funct_1(C_231)) = k1_xboole_0
      | ~ v1_funct_2(k2_funct_1(C_231),k1_xboole_0,A_230)
      | k2_relset_1(A_230,k1_xboole_0,C_231) != k1_xboole_0
      | ~ v2_funct_1(C_231)
      | ~ m1_subset_1(C_231,k1_zfmisc_1(k2_zfmisc_1(A_230,k1_xboole_0)))
      | ~ v1_funct_2(C_231,A_230,k1_xboole_0)
      | ~ v1_funct_1(C_231) ) ),
    inference(resolution,[status(thm)],[c_1335,c_30])).

tff(c_1555,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1('#skF_3')) = k1_xboole_0
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k1_xboole_0,k1_xboole_0)
    | k2_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') != k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1212,c_1548])).

tff(c_1559,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1('#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1213,c_52,c_1210,c_1322,c_1555])).

tff(c_1561,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1330,c_1559])).

tff(c_1562,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_115])).

tff(c_1807,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1752,c_1752,c_1692,c_1692,c_1692,c_1562])).

tff(c_1863,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1862,c_1807])).

tff(c_2038,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2037,c_1863])).

tff(c_2045,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_2038])).

tff(c_2049,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_60,c_52,c_2045])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:37:22 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.74/1.82  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.74/1.86  
% 4.74/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.74/1.86  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.74/1.86  
% 4.74/1.86  %Foreground sorts:
% 4.74/1.86  
% 4.74/1.86  
% 4.74/1.86  %Background operators:
% 4.74/1.86  
% 4.74/1.86  
% 4.74/1.86  %Foreground operators:
% 4.74/1.86  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.74/1.86  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.74/1.86  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.74/1.86  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.74/1.86  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.74/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.74/1.86  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.74/1.86  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.74/1.86  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 4.74/1.86  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.74/1.86  tff('#skF_2', type, '#skF_2': $i).
% 4.74/1.86  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.74/1.86  tff('#skF_3', type, '#skF_3': $i).
% 4.74/1.86  tff('#skF_1', type, '#skF_1': $i).
% 4.74/1.86  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.74/1.86  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.74/1.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.74/1.86  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.74/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.74/1.86  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.74/1.86  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.74/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.74/1.86  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.74/1.86  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.74/1.86  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.74/1.86  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.74/1.86  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.74/1.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.74/1.86  
% 4.74/1.90  tff(f_159, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_2)).
% 4.74/1.90  tff(f_115, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 4.74/1.90  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.74/1.90  tff(f_41, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 4.74/1.90  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.74/1.90  tff(f_123, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.74/1.90  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.74/1.90  tff(f_95, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 4.74/1.90  tff(f_69, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 4.74/1.90  tff(f_111, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 4.74/1.90  tff(f_135, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 4.74/1.90  tff(f_31, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 4.74/1.90  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.74/1.90  tff(c_66, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_159])).
% 4.74/1.90  tff(c_67, plain, (![A_33]: (u1_struct_0(A_33)=k2_struct_0(A_33) | ~l1_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.74/1.90  tff(c_75, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_66, c_67])).
% 4.74/1.90  tff(c_62, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 4.74/1.90  tff(c_74, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_62, c_67])).
% 4.74/1.90  tff(c_56, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_159])).
% 4.74/1.90  tff(c_104, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_74, c_56])).
% 4.74/1.90  tff(c_105, plain, (![C_35, A_36, B_37]: (v1_relat_1(C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.74/1.90  tff(c_109, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_104, c_105])).
% 4.74/1.90  tff(c_60, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_159])).
% 4.74/1.90  tff(c_52, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_159])).
% 4.74/1.90  tff(c_6, plain, (![A_2]: (k2_relat_1(k2_funct_1(A_2))=k1_relat_1(A_2) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.74/1.90  tff(c_1611, plain, (![A_244, B_245, C_246]: (k2_relset_1(A_244, B_245, C_246)=k2_relat_1(C_246) | ~m1_subset_1(C_246, k1_zfmisc_1(k2_zfmisc_1(A_244, B_245))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.74/1.90  tff(c_1615, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_104, c_1611])).
% 4.74/1.90  tff(c_54, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 4.74/1.90  tff(c_85, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_75, c_74, c_54])).
% 4.74/1.90  tff(c_1616, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1615, c_85])).
% 4.74/1.90  tff(c_64, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 4.74/1.90  tff(c_91, plain, (![A_34]: (~v1_xboole_0(u1_struct_0(A_34)) | ~l1_struct_0(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.74/1.90  tff(c_97, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_74, c_91])).
% 4.74/1.90  tff(c_101, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_97])).
% 4.74/1.90  tff(c_102, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_64, c_101])).
% 4.74/1.90  tff(c_1624, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1616, c_102])).
% 4.74/1.90  tff(c_1576, plain, (![C_236, A_237, B_238]: (v4_relat_1(C_236, A_237) | ~m1_subset_1(C_236, k1_zfmisc_1(k2_zfmisc_1(A_237, B_238))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.74/1.90  tff(c_1580, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_104, c_1576])).
% 4.74/1.90  tff(c_1594, plain, (![B_241, A_242]: (k1_relat_1(B_241)=A_242 | ~v1_partfun1(B_241, A_242) | ~v4_relat_1(B_241, A_242) | ~v1_relat_1(B_241))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.74/1.90  tff(c_1597, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1580, c_1594])).
% 4.74/1.90  tff(c_1600, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_1597])).
% 4.74/1.90  tff(c_1610, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_1600])).
% 4.74/1.90  tff(c_58, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_159])).
% 4.74/1.90  tff(c_76, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_58])).
% 4.74/1.90  tff(c_90, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_76])).
% 4.74/1.90  tff(c_1625, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1616, c_90])).
% 4.74/1.90  tff(c_1623, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_1616, c_104])).
% 4.74/1.90  tff(c_1683, plain, (![C_257, A_258, B_259]: (v1_partfun1(C_257, A_258) | ~v1_funct_2(C_257, A_258, B_259) | ~v1_funct_1(C_257) | ~m1_subset_1(C_257, k1_zfmisc_1(k2_zfmisc_1(A_258, B_259))) | v1_xboole_0(B_259))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.74/1.90  tff(c_1686, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_1623, c_1683])).
% 4.74/1.90  tff(c_1689, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1625, c_1686])).
% 4.74/1.90  tff(c_1691, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1624, c_1610, c_1689])).
% 4.74/1.90  tff(c_1692, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_1600])).
% 4.74/1.90  tff(c_1695, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_1692, c_104])).
% 4.74/1.90  tff(c_1747, plain, (![A_261, B_262, C_263]: (k2_relset_1(A_261, B_262, C_263)=k2_relat_1(C_263) | ~m1_subset_1(C_263, k1_zfmisc_1(k2_zfmisc_1(A_261, B_262))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.74/1.90  tff(c_1751, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1695, c_1747])).
% 4.74/1.90  tff(c_1698, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1692, c_85])).
% 4.74/1.90  tff(c_1752, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1751, c_1698])).
% 4.74/1.90  tff(c_1697, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1692, c_90])).
% 4.74/1.90  tff(c_1759, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1752, c_1697])).
% 4.74/1.90  tff(c_1757, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1752, c_1751])).
% 4.74/1.90  tff(c_1758, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_1752, c_1695])).
% 4.74/1.90  tff(c_1877, plain, (![C_290, B_291, A_292]: (m1_subset_1(k2_funct_1(C_290), k1_zfmisc_1(k2_zfmisc_1(B_291, A_292))) | k2_relset_1(A_292, B_291, C_290)!=B_291 | ~v2_funct_1(C_290) | ~m1_subset_1(C_290, k1_zfmisc_1(k2_zfmisc_1(A_292, B_291))) | ~v1_funct_2(C_290, A_292, B_291) | ~v1_funct_1(C_290))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.74/1.90  tff(c_16, plain, (![A_9, B_10, C_11]: (k2_relset_1(A_9, B_10, C_11)=k2_relat_1(C_11) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.74/1.90  tff(c_2027, plain, (![B_302, A_303, C_304]: (k2_relset_1(B_302, A_303, k2_funct_1(C_304))=k2_relat_1(k2_funct_1(C_304)) | k2_relset_1(A_303, B_302, C_304)!=B_302 | ~v2_funct_1(C_304) | ~m1_subset_1(C_304, k1_zfmisc_1(k2_zfmisc_1(A_303, B_302))) | ~v1_funct_2(C_304, A_303, B_302) | ~v1_funct_1(C_304))), inference(resolution, [status(thm)], [c_1877, c_16])).
% 4.74/1.90  tff(c_2033, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1758, c_2027])).
% 4.74/1.90  tff(c_2037, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1759, c_52, c_1757, c_2033])).
% 4.74/1.90  tff(c_1856, plain, (![A_286, B_287, C_288]: (k2_tops_2(A_286, B_287, C_288)=k2_funct_1(C_288) | ~v2_funct_1(C_288) | k2_relset_1(A_286, B_287, C_288)!=B_287 | ~m1_subset_1(C_288, k1_zfmisc_1(k2_zfmisc_1(A_286, B_287))) | ~v1_funct_2(C_288, A_286, B_287) | ~v1_funct_1(C_288))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.74/1.90  tff(c_1859, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1758, c_1856])).
% 4.74/1.90  tff(c_1862, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1759, c_1757, c_52, c_1859])).
% 4.74/1.90  tff(c_166, plain, (![A_52, B_53, C_54]: (k2_relset_1(A_52, B_53, C_54)=k2_relat_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.74/1.90  tff(c_170, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_104, c_166])).
% 4.74/1.90  tff(c_171, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_170, c_85])).
% 4.74/1.90  tff(c_180, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_171, c_102])).
% 4.74/1.90  tff(c_125, plain, (![C_40, A_41, B_42]: (v4_relat_1(C_40, A_41) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.74/1.90  tff(c_129, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_104, c_125])).
% 4.74/1.90  tff(c_136, plain, (![B_47, A_48]: (k1_relat_1(B_47)=A_48 | ~v1_partfun1(B_47, A_48) | ~v4_relat_1(B_47, A_48) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.74/1.90  tff(c_139, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_129, c_136])).
% 4.74/1.90  tff(c_142, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_139])).
% 4.74/1.90  tff(c_143, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_142])).
% 4.74/1.90  tff(c_181, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_171, c_90])).
% 4.74/1.90  tff(c_179, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_171, c_104])).
% 4.74/1.90  tff(c_231, plain, (![C_64, A_65, B_66]: (v1_partfun1(C_64, A_65) | ~v1_funct_2(C_64, A_65, B_66) | ~v1_funct_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))) | v1_xboole_0(B_66))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.74/1.90  tff(c_234, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_179, c_231])).
% 4.74/1.90  tff(c_237, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_181, c_234])).
% 4.74/1.90  tff(c_239, plain, $false, inference(negUnitSimplification, [status(thm)], [c_180, c_143, c_237])).
% 4.74/1.90  tff(c_240, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_142])).
% 4.74/1.90  tff(c_244, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_240, c_104])).
% 4.74/1.90  tff(c_317, plain, (![A_70, B_71, C_72]: (k2_relset_1(A_70, B_71, C_72)=k2_relat_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.74/1.90  tff(c_321, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_244, c_317])).
% 4.74/1.90  tff(c_247, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_240, c_85])).
% 4.74/1.90  tff(c_322, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_321, c_247])).
% 4.74/1.90  tff(c_246, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_240, c_90])).
% 4.74/1.90  tff(c_330, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_322, c_246])).
% 4.74/1.90  tff(c_328, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_322, c_321])).
% 4.74/1.90  tff(c_329, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_322, c_244])).
% 4.74/1.90  tff(c_421, plain, (![A_95, B_96, C_97]: (k2_tops_2(A_95, B_96, C_97)=k2_funct_1(C_97) | ~v2_funct_1(C_97) | k2_relset_1(A_95, B_96, C_97)!=B_96 | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))) | ~v1_funct_2(C_97, A_95, B_96) | ~v1_funct_1(C_97))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.74/1.90  tff(c_424, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_329, c_421])).
% 4.74/1.90  tff(c_427, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_330, c_328, c_52, c_424])).
% 4.74/1.90  tff(c_50, plain, (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 4.74/1.90  tff(c_115, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_75, c_75, c_74, c_74, c_75, c_75, c_74, c_74, c_50])).
% 4.74/1.90  tff(c_116, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_115])).
% 4.74/1.90  tff(c_242, plain, (k1_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_240, c_240, c_116])).
% 4.74/1.90  tff(c_372, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_322, c_322, c_322, c_242])).
% 4.74/1.90  tff(c_428, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_427, c_372])).
% 4.74/1.90  tff(c_110, plain, (![A_38]: (k1_relat_1(A_38)=k1_xboole_0 | k2_relat_1(A_38)!=k1_xboole_0 | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.74/1.90  tff(c_114, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_109, c_110])).
% 4.74/1.90  tff(c_117, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_114])).
% 4.74/1.90  tff(c_118, plain, (![A_39]: (k2_relat_1(A_39)=k1_xboole_0 | k1_relat_1(A_39)!=k1_xboole_0 | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.74/1.90  tff(c_121, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relat_1('#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_109, c_118])).
% 4.74/1.90  tff(c_124, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_117, c_121])).
% 4.74/1.90  tff(c_414, plain, (![C_92, B_93, A_94]: (v1_funct_2(k2_funct_1(C_92), B_93, A_94) | k2_relset_1(A_94, B_93, C_92)!=B_93 | ~v2_funct_1(C_92) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_94, B_93))) | ~v1_funct_2(C_92, A_94, B_93) | ~v1_funct_1(C_92))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.74/1.90  tff(c_417, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_329, c_414])).
% 4.74/1.90  tff(c_420, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_330, c_52, c_328, c_417])).
% 4.74/1.90  tff(c_437, plain, (![C_99, B_100, A_101]: (m1_subset_1(k2_funct_1(C_99), k1_zfmisc_1(k2_zfmisc_1(B_100, A_101))) | k2_relset_1(A_101, B_100, C_99)!=B_100 | ~v2_funct_1(C_99) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_101, B_100))) | ~v1_funct_2(C_99, A_101, B_100) | ~v1_funct_1(C_99))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.74/1.90  tff(c_32, plain, (![B_17, A_16, C_18]: (k1_xboole_0=B_17 | k1_relset_1(A_16, B_17, C_18)=A_16 | ~v1_funct_2(C_18, A_16, B_17) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.74/1.90  tff(c_614, plain, (![A_118, B_119, C_120]: (k1_xboole_0=A_118 | k1_relset_1(B_119, A_118, k2_funct_1(C_120))=B_119 | ~v1_funct_2(k2_funct_1(C_120), B_119, A_118) | k2_relset_1(A_118, B_119, C_120)!=B_119 | ~v2_funct_1(C_120) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))) | ~v1_funct_2(C_120, A_118, B_119) | ~v1_funct_1(C_120))), inference(resolution, [status(thm)], [c_437, c_32])).
% 4.74/1.90  tff(c_620, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_329, c_614])).
% 4.74/1.90  tff(c_624, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_330, c_52, c_328, c_420, c_620])).
% 4.74/1.90  tff(c_626, plain, $false, inference(negUnitSimplification, [status(thm)], [c_428, c_124, c_624])).
% 4.74/1.90  tff(c_628, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_114])).
% 4.74/1.90  tff(c_627, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_114])).
% 4.74/1.90  tff(c_654, plain, (![B_128]: (v1_partfun1(B_128, k1_relat_1(B_128)) | ~v4_relat_1(B_128, k1_relat_1(B_128)) | ~v1_relat_1(B_128))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.74/1.90  tff(c_657, plain, (v1_partfun1('#skF_3', k1_relat_1('#skF_3')) | ~v4_relat_1('#skF_3', k1_xboole_0) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_627, c_654])).
% 4.74/1.90  tff(c_659, plain, (v1_partfun1('#skF_3', k1_xboole_0) | ~v4_relat_1('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_109, c_627, c_657])).
% 4.74/1.90  tff(c_667, plain, (~v4_relat_1('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_659])).
% 4.74/1.90  tff(c_691, plain, (![A_134, B_135, C_136]: (k2_relset_1(A_134, B_135, C_136)=k2_relat_1(C_136) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.74/1.90  tff(c_694, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_104, c_691])).
% 4.74/1.90  tff(c_696, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_628, c_694])).
% 4.74/1.90  tff(c_697, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_696, c_85])).
% 4.74/1.90  tff(c_708, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_697, c_90])).
% 4.74/1.90  tff(c_706, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_697, c_104])).
% 4.74/1.90  tff(c_24, plain, (![C_18, A_16]: (k1_xboole_0=C_18 | ~v1_funct_2(C_18, A_16, k1_xboole_0) | k1_xboole_0=A_16 | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.74/1.90  tff(c_739, plain, (k1_xboole_0='#skF_3' | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k1_xboole_0) | k2_struct_0('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_706, c_24])).
% 4.74/1.90  tff(c_755, plain, (k1_xboole_0='#skF_3' | k2_struct_0('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_708, c_739])).
% 4.74/1.90  tff(c_756, plain, (k2_struct_0('#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_755])).
% 4.74/1.90  tff(c_649, plain, (![C_125, A_126, B_127]: (v4_relat_1(C_125, A_126) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_126, B_127))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.74/1.90  tff(c_653, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_104, c_649])).
% 4.74/1.90  tff(c_762, plain, (v4_relat_1('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_756, c_653])).
% 4.74/1.90  tff(c_766, plain, $false, inference(negUnitSimplification, [status(thm)], [c_667, c_762])).
% 4.74/1.90  tff(c_767, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_755])).
% 4.74/1.90  tff(c_707, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_697, c_102])).
% 4.74/1.90  tff(c_776, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_767, c_707])).
% 4.74/1.90  tff(c_660, plain, (![B_129, A_130]: (k1_relat_1(B_129)=A_130 | ~v1_partfun1(B_129, A_130) | ~v4_relat_1(B_129, A_130) | ~v1_relat_1(B_129))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.74/1.90  tff(c_663, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_653, c_660])).
% 4.74/1.90  tff(c_666, plain, (k2_struct_0('#skF_1')=k1_xboole_0 | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_627, c_663])).
% 4.74/1.90  tff(c_668, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_666])).
% 4.74/1.90  tff(c_772, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_767, c_708])).
% 4.74/1.90  tff(c_774, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_767, c_706])).
% 4.74/1.90  tff(c_892, plain, (![C_156, A_157, B_158]: (v1_partfun1(C_156, A_157) | ~v1_funct_2(C_156, A_157, B_158) | ~v1_funct_1(C_156) | ~m1_subset_1(C_156, k1_zfmisc_1(k2_zfmisc_1(A_157, B_158))) | v1_xboole_0(B_158))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.74/1.90  tff(c_895, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), '#skF_3') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_774, c_892])).
% 4.74/1.90  tff(c_898, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_772, c_895])).
% 4.74/1.90  tff(c_900, plain, $false, inference(negUnitSimplification, [status(thm)], [c_776, c_668, c_898])).
% 4.74/1.90  tff(c_901, plain, (k2_struct_0('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_666])).
% 4.74/1.90  tff(c_903, plain, (v4_relat_1('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_901, c_653])).
% 4.74/1.90  tff(c_911, plain, $false, inference(negUnitSimplification, [status(thm)], [c_667, c_903])).
% 4.74/1.90  tff(c_912, plain, (v1_partfun1('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_659])).
% 4.74/1.90  tff(c_942, plain, (![A_161, B_162, C_163]: (k2_relset_1(A_161, B_162, C_163)=k2_relat_1(C_163) | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(A_161, B_162))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.74/1.90  tff(c_945, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_104, c_942])).
% 4.74/1.90  tff(c_947, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_628, c_945])).
% 4.74/1.90  tff(c_948, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_947, c_85])).
% 4.74/1.90  tff(c_958, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_948, c_90])).
% 4.74/1.90  tff(c_956, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_948, c_104])).
% 4.74/1.90  tff(c_999, plain, (![C_165, A_166]: (k1_xboole_0=C_165 | ~v1_funct_2(C_165, A_166, k1_xboole_0) | k1_xboole_0=A_166 | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1(A_166, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.74/1.90  tff(c_1002, plain, (k1_xboole_0='#skF_3' | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k1_xboole_0) | k2_struct_0('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_956, c_999])).
% 4.74/1.90  tff(c_1005, plain, (k1_xboole_0='#skF_3' | k2_struct_0('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_958, c_1002])).
% 4.74/1.90  tff(c_1006, plain, (k2_struct_0('#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1005])).
% 4.74/1.90  tff(c_929, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_666])).
% 4.74/1.90  tff(c_1011, plain, (~v1_partfun1('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1006, c_929])).
% 4.74/1.90  tff(c_1017, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_912, c_1011])).
% 4.74/1.90  tff(c_1018, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_1005])).
% 4.74/1.90  tff(c_957, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_948, c_102])).
% 4.74/1.90  tff(c_1028, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1018, c_957])).
% 4.74/1.90  tff(c_1024, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1018, c_958])).
% 4.74/1.90  tff(c_1022, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1018, c_956])).
% 4.74/1.90  tff(c_1134, plain, (![C_176, A_177, B_178]: (v1_partfun1(C_176, A_177) | ~v1_funct_2(C_176, A_177, B_178) | ~v1_funct_1(C_176) | ~m1_subset_1(C_176, k1_zfmisc_1(k2_zfmisc_1(A_177, B_178))) | v1_xboole_0(B_178))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.74/1.90  tff(c_1137, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), '#skF_3') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_1022, c_1134])).
% 4.74/1.90  tff(c_1140, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1024, c_1137])).
% 4.74/1.90  tff(c_1142, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1028, c_929, c_1140])).
% 4.74/1.90  tff(c_1143, plain, (k2_struct_0('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_666])).
% 4.74/1.90  tff(c_1159, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_1143, c_104])).
% 4.74/1.90  tff(c_1199, plain, (![A_181, B_182, C_183]: (k2_relset_1(A_181, B_182, C_183)=k2_relat_1(C_183) | ~m1_subset_1(C_183, k1_zfmisc_1(k2_zfmisc_1(A_181, B_182))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.74/1.90  tff(c_1202, plain, (k2_relset_1(k1_xboole_0, k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1159, c_1199])).
% 4.74/1.90  tff(c_1204, plain, (k2_relset_1(k1_xboole_0, k2_struct_0('#skF_2'), '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_628, c_1202])).
% 4.74/1.90  tff(c_1162, plain, (k2_relset_1(k1_xboole_0, k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1143, c_85])).
% 4.74/1.90  tff(c_1205, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1204, c_1162])).
% 4.74/1.90  tff(c_1161, plain, (v1_funct_2('#skF_3', k1_xboole_0, k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1143, c_90])).
% 4.74/1.90  tff(c_1213, plain, (v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1205, c_1161])).
% 4.74/1.90  tff(c_1210, plain, (k2_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1205, c_1204])).
% 4.74/1.90  tff(c_1212, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_1205, c_1159])).
% 4.74/1.90  tff(c_1323, plain, (![A_206, B_207, C_208]: (k2_tops_2(A_206, B_207, C_208)=k2_funct_1(C_208) | ~v2_funct_1(C_208) | k2_relset_1(A_206, B_207, C_208)!=B_207 | ~m1_subset_1(C_208, k1_zfmisc_1(k2_zfmisc_1(A_206, B_207))) | ~v1_funct_2(C_208, A_206, B_207) | ~v1_funct_1(C_208))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.74/1.90  tff(c_1326, plain, (k2_tops_2(k1_xboole_0, k1_xboole_0, '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3')!=k1_xboole_0 | ~v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1212, c_1323])).
% 4.74/1.90  tff(c_1329, plain, (k2_tops_2(k1_xboole_0, k1_xboole_0, '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1213, c_1210, c_52, c_1326])).
% 4.74/1.90  tff(c_1158, plain, (k1_relset_1(k2_struct_0('#skF_2'), k1_xboole_0, k2_tops_2(k1_xboole_0, k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1143, c_1143, c_116])).
% 4.74/1.90  tff(c_1211, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, k2_tops_2(k1_xboole_0, k1_xboole_0, '#skF_3'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1205, c_1205, c_1205, c_1158])).
% 4.74/1.90  tff(c_1330, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, k2_funct_1('#skF_3'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1329, c_1211])).
% 4.74/1.90  tff(c_1316, plain, (![C_203, B_204, A_205]: (v1_funct_2(k2_funct_1(C_203), B_204, A_205) | k2_relset_1(A_205, B_204, C_203)!=B_204 | ~v2_funct_1(C_203) | ~m1_subset_1(C_203, k1_zfmisc_1(k2_zfmisc_1(A_205, B_204))) | ~v1_funct_2(C_203, A_205, B_204) | ~v1_funct_1(C_203))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.74/1.90  tff(c_1319, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_xboole_0, k1_xboole_0) | k2_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3')!=k1_xboole_0 | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1212, c_1316])).
% 4.74/1.90  tff(c_1322, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1213, c_52, c_1210, c_1319])).
% 4.74/1.90  tff(c_1335, plain, (![C_209, B_210, A_211]: (m1_subset_1(k2_funct_1(C_209), k1_zfmisc_1(k2_zfmisc_1(B_210, A_211))) | k2_relset_1(A_211, B_210, C_209)!=B_210 | ~v2_funct_1(C_209) | ~m1_subset_1(C_209, k1_zfmisc_1(k2_zfmisc_1(A_211, B_210))) | ~v1_funct_2(C_209, A_211, B_210) | ~v1_funct_1(C_209))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.74/1.90  tff(c_30, plain, (![B_17, C_18]: (k1_relset_1(k1_xboole_0, B_17, C_18)=k1_xboole_0 | ~v1_funct_2(C_18, k1_xboole_0, B_17) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_17))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.74/1.90  tff(c_1548, plain, (![A_230, C_231]: (k1_relset_1(k1_xboole_0, A_230, k2_funct_1(C_231))=k1_xboole_0 | ~v1_funct_2(k2_funct_1(C_231), k1_xboole_0, A_230) | k2_relset_1(A_230, k1_xboole_0, C_231)!=k1_xboole_0 | ~v2_funct_1(C_231) | ~m1_subset_1(C_231, k1_zfmisc_1(k2_zfmisc_1(A_230, k1_xboole_0))) | ~v1_funct_2(C_231, A_230, k1_xboole_0) | ~v1_funct_1(C_231))), inference(resolution, [status(thm)], [c_1335, c_30])).
% 4.74/1.90  tff(c_1555, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, k2_funct_1('#skF_3'))=k1_xboole_0 | ~v1_funct_2(k2_funct_1('#skF_3'), k1_xboole_0, k1_xboole_0) | k2_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3')!=k1_xboole_0 | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1212, c_1548])).
% 4.74/1.90  tff(c_1559, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, k2_funct_1('#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1213, c_52, c_1210, c_1322, c_1555])).
% 4.74/1.90  tff(c_1561, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1330, c_1559])).
% 4.74/1.90  tff(c_1562, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_115])).
% 4.74/1.90  tff(c_1807, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1752, c_1752, c_1692, c_1692, c_1692, c_1562])).
% 4.74/1.90  tff(c_1863, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1862, c_1807])).
% 4.74/1.90  tff(c_2038, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2037, c_1863])).
% 4.74/1.90  tff(c_2045, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6, c_2038])).
% 4.74/1.90  tff(c_2049, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_109, c_60, c_52, c_2045])).
% 4.74/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.74/1.90  
% 4.74/1.90  Inference rules
% 4.74/1.90  ----------------------
% 4.74/1.90  #Ref     : 0
% 4.74/1.90  #Sup     : 410
% 4.74/1.90  #Fact    : 0
% 4.74/1.90  #Define  : 0
% 4.74/1.90  #Split   : 16
% 4.74/1.90  #Chain   : 0
% 4.74/1.90  #Close   : 0
% 4.74/1.90  
% 4.74/1.90  Ordering : KBO
% 4.74/1.90  
% 4.74/1.90  Simplification rules
% 4.74/1.90  ----------------------
% 4.74/1.90  #Subsume      : 27
% 4.74/1.90  #Demod        : 586
% 4.74/1.90  #Tautology    : 256
% 4.74/1.90  #SimpNegUnit  : 36
% 4.74/1.90  #BackRed      : 136
% 4.74/1.90  
% 4.74/1.90  #Partial instantiations: 0
% 4.74/1.90  #Strategies tried      : 1
% 4.74/1.90  
% 4.74/1.90  Timing (in seconds)
% 4.74/1.90  ----------------------
% 4.74/1.90  Preprocessing        : 0.36
% 4.74/1.90  Parsing              : 0.19
% 4.74/1.90  CNF conversion       : 0.02
% 4.74/1.90  Main loop            : 0.71
% 4.74/1.90  Inferencing          : 0.25
% 4.74/1.90  Reduction            : 0.24
% 4.74/1.90  Demodulation         : 0.17
% 4.74/1.90  BG Simplification    : 0.03
% 4.74/1.90  Subsumption          : 0.11
% 4.74/1.90  Abstraction          : 0.05
% 4.74/1.90  MUC search           : 0.00
% 4.74/1.90  Cooper               : 0.00
% 4.74/1.90  Total                : 1.16
% 4.74/1.90  Index Insertion      : 0.00
% 4.74/1.90  Index Deletion       : 0.00
% 4.74/1.90  Index Matching       : 0.00
% 4.74/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
