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
% DateTime   : Thu Dec  3 10:23:13 EST 2020

% Result     : Theorem 6.95s
% Output     : CNFRefutation 7.37s
% Verified   : 
% Statistics : Number of formulae       :  269 (8500 expanded)
%              Number of leaves         :   47 (2953 expanded)
%              Depth                    :   21
%              Number of atoms          :  547 (24516 expanded)
%              Number of equality atoms :  175 (8048 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(f_36,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_216,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).

tff(f_172,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_54,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_135,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_152,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | v1_partfun1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

tff(f_180,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_168,axiom,(
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

tff(f_192,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_127,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_38,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).

tff(c_10,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_88,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_124,plain,(
    ! [A_58] :
      ( u1_struct_0(A_58) = k2_struct_0(A_58)
      | ~ l1_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_132,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_88,c_124])).

tff(c_84,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_131,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_84,c_124])).

tff(c_78,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_162,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_131,c_78])).

tff(c_163,plain,(
    ! [C_61,A_62,B_63] :
      ( v1_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_175,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_162,c_163])).

tff(c_82,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_74,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_16,plain,(
    ! [A_8] :
      ( k2_relat_1(k2_funct_1(A_8)) = k1_relat_1(A_8)
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1821,plain,(
    ! [C_289,A_290,B_291] :
      ( v4_relat_1(C_289,A_290)
      | ~ m1_subset_1(C_289,k1_zfmisc_1(k2_zfmisc_1(A_290,B_291))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1835,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_162,c_1821])).

tff(c_1963,plain,(
    ! [B_317,A_318] :
      ( k1_relat_1(B_317) = A_318
      | ~ v1_partfun1(B_317,A_318)
      | ~ v4_relat_1(B_317,A_318)
      | ~ v1_relat_1(B_317) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1966,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1835,c_1963])).

tff(c_1972,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_1966])).

tff(c_2013,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1972])).

tff(c_2019,plain,(
    ! [A_323,B_324,C_325] :
      ( k2_relset_1(A_323,B_324,C_325) = k2_relat_1(C_325)
      | ~ m1_subset_1(C_325,k1_zfmisc_1(k2_zfmisc_1(A_323,B_324))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2033,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_162,c_2019])).

tff(c_76,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_156,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_131,c_76])).

tff(c_2042,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2033,c_156])).

tff(c_80,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_133,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_80])).

tff(c_161,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_133])).

tff(c_2053,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2042,c_161])).

tff(c_2052,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2042,c_162])).

tff(c_2156,plain,(
    ! [B_340,C_341,A_342] :
      ( k1_xboole_0 = B_340
      | v1_partfun1(C_341,A_342)
      | ~ v1_funct_2(C_341,A_342,B_340)
      | ~ m1_subset_1(C_341,k1_zfmisc_1(k2_zfmisc_1(A_342,B_340)))
      | ~ v1_funct_1(C_341) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_2159,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2052,c_2156])).

tff(c_2172,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_2053,c_2159])).

tff(c_2173,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_2013,c_2172])).

tff(c_86,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_143,plain,(
    ! [A_60] :
      ( ~ v1_xboole_0(u1_struct_0(A_60))
      | ~ l1_struct_0(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_149,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_143])).

tff(c_153,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_149])).

tff(c_154,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_153])).

tff(c_2054,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2042,c_154])).

tff(c_2183,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2173,c_2054])).

tff(c_2189,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2183])).

tff(c_2190,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1972])).

tff(c_2196,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2190,c_162])).

tff(c_30,plain,(
    ! [A_23,B_24,C_25] :
      ( k2_relset_1(A_23,B_24,C_25) = k2_relat_1(C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2275,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2196,c_30])).

tff(c_2198,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2190,c_156])).

tff(c_2287,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2275,c_2198])).

tff(c_2197,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2190,c_161])).

tff(c_2294,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2287,c_2197])).

tff(c_2292,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2287,c_2275])).

tff(c_2293,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2287,c_2196])).

tff(c_2636,plain,(
    ! [C_400,B_401,A_402] :
      ( m1_subset_1(k2_funct_1(C_400),k1_zfmisc_1(k2_zfmisc_1(B_401,A_402)))
      | k2_relset_1(A_402,B_401,C_400) != B_401
      | ~ v2_funct_1(C_400)
      | ~ m1_subset_1(C_400,k1_zfmisc_1(k2_zfmisc_1(A_402,B_401)))
      | ~ v1_funct_2(C_400,A_402,B_401)
      | ~ v1_funct_1(C_400) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_3294,plain,(
    ! [B_479,A_480,C_481] :
      ( k2_relset_1(B_479,A_480,k2_funct_1(C_481)) = k2_relat_1(k2_funct_1(C_481))
      | k2_relset_1(A_480,B_479,C_481) != B_479
      | ~ v2_funct_1(C_481)
      | ~ m1_subset_1(C_481,k1_zfmisc_1(k2_zfmisc_1(A_480,B_479)))
      | ~ v1_funct_2(C_481,A_480,B_479)
      | ~ v1_funct_1(C_481) ) ),
    inference(resolution,[status(thm)],[c_2636,c_30])).

tff(c_3300,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2293,c_3294])).

tff(c_3314,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_2294,c_74,c_2292,c_3300])).

tff(c_2595,plain,(
    ! [A_393,B_394,C_395] :
      ( k2_tops_2(A_393,B_394,C_395) = k2_funct_1(C_395)
      | ~ v2_funct_1(C_395)
      | k2_relset_1(A_393,B_394,C_395) != B_394
      | ~ m1_subset_1(C_395,k1_zfmisc_1(k2_zfmisc_1(A_393,B_394)))
      | ~ v1_funct_2(C_395,A_393,B_394)
      | ~ v1_funct_1(C_395) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_2598,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2293,c_2595])).

tff(c_2611,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_2294,c_2292,c_74,c_2598])).

tff(c_227,plain,(
    ! [C_74,A_75,B_76] :
      ( v4_relat_1(C_74,A_75)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_241,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_162,c_227])).

tff(c_363,plain,(
    ! [B_103,A_104] :
      ( k1_relat_1(B_103) = A_104
      | ~ v1_partfun1(B_103,A_104)
      | ~ v4_relat_1(B_103,A_104)
      | ~ v1_relat_1(B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_366,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_241,c_363])).

tff(c_372,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_366])).

tff(c_402,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_372])).

tff(c_421,plain,(
    ! [A_109,B_110,C_111] :
      ( k2_relset_1(A_109,B_110,C_111) = k2_relat_1(C_111)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_435,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_162,c_421])).

tff(c_449,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_156])).

tff(c_459,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_449,c_161])).

tff(c_458,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_449,c_162])).

tff(c_569,plain,(
    ! [B_127,C_128,A_129] :
      ( k1_xboole_0 = B_127
      | v1_partfun1(C_128,A_129)
      | ~ v1_funct_2(C_128,A_129,B_127)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_129,B_127)))
      | ~ v1_funct_1(C_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_572,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_458,c_569])).

tff(c_585,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_459,c_572])).

tff(c_586,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_402,c_585])).

tff(c_460,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_449,c_154])).

tff(c_596,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_586,c_460])).

tff(c_602,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_596])).

tff(c_603,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_372])).

tff(c_608,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_603,c_162])).

tff(c_694,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_608,c_30])).

tff(c_610,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_603,c_156])).

tff(c_710,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_694,c_610])).

tff(c_609,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_603,c_161])).

tff(c_717,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_710,c_609])).

tff(c_715,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_710,c_694])).

tff(c_716,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_710,c_608])).

tff(c_1000,plain,(
    ! [A_177,B_178,C_179] :
      ( k2_tops_2(A_177,B_178,C_179) = k2_funct_1(C_179)
      | ~ v2_funct_1(C_179)
      | k2_relset_1(A_177,B_178,C_179) != B_178
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1(A_177,B_178)))
      | ~ v1_funct_2(C_179,A_177,B_178)
      | ~ v1_funct_1(C_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_1003,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_716,c_1000])).

tff(c_1016,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_717,c_715,c_74,c_1003])).

tff(c_72,plain,
    ( k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_211,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_132,c_131,c_131,c_132,c_132,c_131,c_131,c_72])).

tff(c_212,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_211])).

tff(c_606,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_603,c_603,c_212])).

tff(c_823,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_710,c_710,c_710,c_606])).

tff(c_1019,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1016,c_823])).

tff(c_966,plain,(
    ! [C_170,B_171,A_172] :
      ( v1_funct_2(k2_funct_1(C_170),B_171,A_172)
      | k2_relset_1(A_172,B_171,C_170) != B_171
      | ~ v2_funct_1(C_170)
      | ~ m1_subset_1(C_170,k1_zfmisc_1(k2_zfmisc_1(A_172,B_171)))
      | ~ v1_funct_2(C_170,A_172,B_171)
      | ~ v1_funct_1(C_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_969,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_716,c_966])).

tff(c_982,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_717,c_74,c_715,c_969])).

tff(c_1044,plain,(
    ! [C_186,B_187,A_188] :
      ( m1_subset_1(k2_funct_1(C_186),k1_zfmisc_1(k2_zfmisc_1(B_187,A_188)))
      | k2_relset_1(A_188,B_187,C_186) != B_187
      | ~ v2_funct_1(C_186)
      | ~ m1_subset_1(C_186,k1_zfmisc_1(k2_zfmisc_1(A_188,B_187)))
      | ~ v1_funct_2(C_186,A_188,B_187)
      | ~ v1_funct_1(C_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_50,plain,(
    ! [B_35,A_34,C_36] :
      ( k1_xboole_0 = B_35
      | k1_relset_1(A_34,B_35,C_36) = A_34
      | ~ v1_funct_2(C_36,A_34,B_35)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_1760,plain,(
    ! [A_282,B_283,C_284] :
      ( k1_xboole_0 = A_282
      | k1_relset_1(B_283,A_282,k2_funct_1(C_284)) = B_283
      | ~ v1_funct_2(k2_funct_1(C_284),B_283,A_282)
      | k2_relset_1(A_282,B_283,C_284) != B_283
      | ~ v2_funct_1(C_284)
      | ~ m1_subset_1(C_284,k1_zfmisc_1(k2_zfmisc_1(A_282,B_283)))
      | ~ v1_funct_2(C_284,A_282,B_283)
      | ~ v1_funct_1(C_284) ) ),
    inference(resolution,[status(thm)],[c_1044,c_50])).

tff(c_1766,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_716,c_1760])).

tff(c_1780,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_717,c_74,c_715,c_982,c_1766])).

tff(c_1781,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_1019,c_1780])).

tff(c_146,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_143])).

tff(c_151,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_146])).

tff(c_155,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_151])).

tff(c_611,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_603,c_155])).

tff(c_1798,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1781,c_611])).

tff(c_1804,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1798])).

tff(c_1805,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_2192,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2190,c_2190,c_2190,c_1805])).

tff(c_2405,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2287,c_2287,c_2192])).

tff(c_2615,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2611,c_2405])).

tff(c_3317,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3314,c_2615])).

tff(c_3324,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_3317])).

tff(c_3328,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_82,c_74,c_3324])).

tff(c_3330,plain,(
    v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_3334,plain,(
    k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3330,c_4])).

tff(c_3342,plain,(
    u1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3334,c_132])).

tff(c_3358,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_3342,c_131,c_78])).

tff(c_8,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_3444,plain,(
    ! [C_499,B_500,A_501] :
      ( v1_xboole_0(C_499)
      | ~ m1_subset_1(C_499,k1_zfmisc_1(k2_zfmisc_1(B_500,A_501)))
      | ~ v1_xboole_0(A_501) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_3454,plain,(
    ! [C_499] :
      ( v1_xboole_0(C_499)
      | ~ m1_subset_1(C_499,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_3444])).

tff(c_3460,plain,(
    ! [C_503] :
      ( v1_xboole_0(C_503)
      | ~ m1_subset_1(C_503,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_3454])).

tff(c_3468,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_3358,c_3460])).

tff(c_3474,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3468,c_4])).

tff(c_12,plain,(
    ! [A_4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_40,plain,(
    ! [A_34] :
      ( v1_funct_2(k1_xboole_0,A_34,k1_xboole_0)
      | k1_xboole_0 = A_34
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_34,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_90,plain,(
    ! [A_34] :
      ( v1_funct_2(k1_xboole_0,A_34,k1_xboole_0)
      | k1_xboole_0 = A_34 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_40])).

tff(c_3488,plain,(
    ! [A_34] :
      ( v1_funct_2('#skF_3',A_34,'#skF_3')
      | A_34 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3474,c_3474,c_3474,c_90])).

tff(c_3490,plain,(
    ! [A_4] : m1_subset_1('#skF_3',k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3474,c_12])).

tff(c_3754,plain,(
    ! [A_539,B_540,C_541] :
      ( k2_relset_1(A_539,B_540,C_541) = k2_relat_1(C_541)
      | ~ m1_subset_1(C_541,k1_zfmisc_1(k2_zfmisc_1(A_539,B_540))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_3765,plain,(
    ! [A_539,B_540] : k2_relset_1(A_539,B_540,'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3490,c_3754])).

tff(c_4044,plain,(
    ! [A_589,B_590,C_591] :
      ( k2_tops_2(A_589,B_590,C_591) = k2_funct_1(C_591)
      | ~ v2_funct_1(C_591)
      | k2_relset_1(A_589,B_590,C_591) != B_590
      | ~ m1_subset_1(C_591,k1_zfmisc_1(k2_zfmisc_1(A_589,B_590)))
      | ~ v1_funct_2(C_591,A_589,B_590)
      | ~ v1_funct_1(C_591) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_4048,plain,(
    ! [A_589,B_590] :
      ( k2_tops_2(A_589,B_590,'#skF_3') = k2_funct_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | k2_relset_1(A_589,B_590,'#skF_3') != B_590
      | ~ v1_funct_2('#skF_3',A_589,B_590)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_3490,c_4044])).

tff(c_4059,plain,(
    ! [A_592,B_593] :
      ( k2_tops_2(A_592,B_593,'#skF_3') = k2_funct_1('#skF_3')
      | k2_relat_1('#skF_3') != B_593
      | ~ v1_funct_2('#skF_3',A_592,B_593) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_3765,c_74,c_4048])).

tff(c_4075,plain,(
    ! [A_34] :
      ( k2_tops_2(A_34,'#skF_3','#skF_3') = k2_funct_1('#skF_3')
      | k2_relat_1('#skF_3') != '#skF_3'
      | A_34 = '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_3488,c_4059])).

tff(c_4081,plain,(
    k2_relat_1('#skF_3') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4075])).

tff(c_3700,plain,(
    ! [C_532,A_533,B_534] :
      ( v1_partfun1(C_532,A_533)
      | ~ m1_subset_1(C_532,k1_zfmisc_1(k2_zfmisc_1(A_533,B_534)))
      | ~ v1_xboole_0(A_533) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_3714,plain,(
    ! [A_535] :
      ( v1_partfun1('#skF_3',A_535)
      | ~ v1_xboole_0(A_535) ) ),
    inference(resolution,[status(thm)],[c_3490,c_3700])).

tff(c_3374,plain,(
    ! [C_484,A_485,B_486] :
      ( v1_relat_1(C_484)
      | ~ m1_subset_1(C_484,k1_zfmisc_1(k2_zfmisc_1(A_485,B_486))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_3384,plain,(
    ! [C_487] :
      ( v1_relat_1(C_487)
      | ~ m1_subset_1(C_487,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_3374])).

tff(c_3392,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3358,c_3384])).

tff(c_3395,plain,(
    ! [C_488,A_489,B_490] :
      ( v4_relat_1(C_488,A_489)
      | ~ m1_subset_1(C_488,k1_zfmisc_1(k2_zfmisc_1(A_489,B_490))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3421,plain,(
    ! [C_493,A_494] :
      ( v4_relat_1(C_493,A_494)
      | ~ m1_subset_1(C_493,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_3395])).

tff(c_3427,plain,(
    ! [A_494] : v4_relat_1('#skF_3',A_494) ),
    inference(resolution,[status(thm)],[c_3358,c_3421])).

tff(c_3666,plain,(
    ! [B_527,A_528] :
      ( k1_relat_1(B_527) = A_528
      | ~ v1_partfun1(B_527,A_528)
      | ~ v4_relat_1(B_527,A_528)
      | ~ v1_relat_1(B_527) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_3669,plain,(
    ! [A_494] :
      ( k1_relat_1('#skF_3') = A_494
      | ~ v1_partfun1('#skF_3',A_494)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_3427,c_3666])).

tff(c_3672,plain,(
    ! [A_494] :
      ( k1_relat_1('#skF_3') = A_494
      | ~ v1_partfun1('#skF_3',A_494) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3392,c_3669])).

tff(c_3719,plain,(
    ! [A_536] :
      ( k1_relat_1('#skF_3') = A_536
      | ~ v1_xboole_0(A_536) ) ),
    inference(resolution,[status(thm)],[c_3714,c_3672])).

tff(c_3723,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3468,c_3719])).

tff(c_3335,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_132,c_76])).

tff(c_3340,plain,(
    k2_relset_1(k1_xboole_0,k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3334,c_3335])).

tff(c_3483,plain,(
    k2_relset_1('#skF_3',k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3474,c_3340])).

tff(c_3766,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3765,c_3483])).

tff(c_3357,plain,(
    v1_funct_2('#skF_3',k1_xboole_0,k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3342,c_133])).

tff(c_3485,plain,(
    v1_funct_2('#skF_3','#skF_3',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3474,c_3357])).

tff(c_3775,plain,(
    v1_funct_2('#skF_3','#skF_3',k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3766,c_3485])).

tff(c_4082,plain,(
    ! [C_594,B_595,A_596] :
      ( m1_subset_1(k2_funct_1(C_594),k1_zfmisc_1(k2_zfmisc_1(B_595,A_596)))
      | k2_relset_1(A_596,B_595,C_594) != B_595
      | ~ v2_funct_1(C_594)
      | ~ m1_subset_1(C_594,k1_zfmisc_1(k2_zfmisc_1(A_596,B_595)))
      | ~ v1_funct_2(C_594,A_596,B_595)
      | ~ v1_funct_1(C_594) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_28,plain,(
    ! [C_22,B_20,A_19] :
      ( v1_xboole_0(C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(B_20,A_19)))
      | ~ v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_4632,plain,(
    ! [C_654,A_655,B_656] :
      ( v1_xboole_0(k2_funct_1(C_654))
      | ~ v1_xboole_0(A_655)
      | k2_relset_1(A_655,B_656,C_654) != B_656
      | ~ v2_funct_1(C_654)
      | ~ m1_subset_1(C_654,k1_zfmisc_1(k2_zfmisc_1(A_655,B_656)))
      | ~ v1_funct_2(C_654,A_655,B_656)
      | ~ v1_funct_1(C_654) ) ),
    inference(resolution,[status(thm)],[c_4082,c_28])).

tff(c_4639,plain,(
    ! [A_655,B_656] :
      ( v1_xboole_0(k2_funct_1('#skF_3'))
      | ~ v1_xboole_0(A_655)
      | k2_relset_1(A_655,B_656,'#skF_3') != B_656
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_2('#skF_3',A_655,B_656)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_3490,c_4632])).

tff(c_4649,plain,(
    ! [A_655,B_656] :
      ( v1_xboole_0(k2_funct_1('#skF_3'))
      | ~ v1_xboole_0(A_655)
      | k2_relat_1('#skF_3') != B_656
      | ~ v1_funct_2('#skF_3',A_655,B_656) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_74,c_3765,c_4639])).

tff(c_4654,plain,(
    ! [A_657,B_658] :
      ( ~ v1_xboole_0(A_657)
      | k2_relat_1('#skF_3') != B_658
      | ~ v1_funct_2('#skF_3',A_657,B_658) ) ),
    inference(splitLeft,[status(thm)],[c_4649])).

tff(c_4663,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_3775,c_4654])).

tff(c_4674,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3468,c_4663])).

tff(c_4675,plain,(
    v1_xboole_0(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_4649])).

tff(c_3492,plain,(
    ! [A_1] :
      ( A_1 = '#skF_3'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3474,c_4])).

tff(c_4683,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_4675,c_3492])).

tff(c_20,plain,(
    ! [C_11,A_9,B_10] :
      ( v1_relat_1(C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4228,plain,(
    ! [C_605,A_606,B_607] :
      ( v1_relat_1(k2_funct_1(C_605))
      | k2_relset_1(A_606,B_607,C_605) != B_607
      | ~ v2_funct_1(C_605)
      | ~ m1_subset_1(C_605,k1_zfmisc_1(k2_zfmisc_1(A_606,B_607)))
      | ~ v1_funct_2(C_605,A_606,B_607)
      | ~ v1_funct_1(C_605) ) ),
    inference(resolution,[status(thm)],[c_4082,c_20])).

tff(c_4235,plain,(
    ! [A_606,B_607] :
      ( v1_relat_1(k2_funct_1('#skF_3'))
      | k2_relset_1(A_606,B_607,'#skF_3') != B_607
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_2('#skF_3',A_606,B_607)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_3490,c_4228])).

tff(c_4245,plain,(
    ! [B_607,A_606] :
      ( v1_relat_1(k2_funct_1('#skF_3'))
      | k2_relat_1('#skF_3') != B_607
      | ~ v1_funct_2('#skF_3',A_606,B_607) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_74,c_3765,c_4235])).

tff(c_4247,plain,(
    ! [A_606] : ~ v1_funct_2('#skF_3',A_606,k2_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_4245])).

tff(c_4249,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4247,c_3775])).

tff(c_4250,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_4245])).

tff(c_24,plain,(
    ! [C_14,A_12,B_13] :
      ( v4_relat_1(C_14,A_12)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4251,plain,(
    ! [C_608,B_609,A_610] :
      ( v4_relat_1(k2_funct_1(C_608),B_609)
      | k2_relset_1(A_610,B_609,C_608) != B_609
      | ~ v2_funct_1(C_608)
      | ~ m1_subset_1(C_608,k1_zfmisc_1(k2_zfmisc_1(A_610,B_609)))
      | ~ v1_funct_2(C_608,A_610,B_609)
      | ~ v1_funct_1(C_608) ) ),
    inference(resolution,[status(thm)],[c_4082,c_24])).

tff(c_4258,plain,(
    ! [B_609,A_610] :
      ( v4_relat_1(k2_funct_1('#skF_3'),B_609)
      | k2_relset_1(A_610,B_609,'#skF_3') != B_609
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_2('#skF_3',A_610,B_609)
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_3490,c_4251])).

tff(c_4270,plain,(
    ! [B_611,A_612] :
      ( v4_relat_1(k2_funct_1('#skF_3'),B_611)
      | k2_relat_1('#skF_3') != B_611
      | ~ v1_funct_2('#skF_3',A_612,B_611) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_74,c_3765,c_4258])).

tff(c_4281,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3775,c_4270])).

tff(c_54,plain,(
    ! [B_38,A_37] :
      ( k1_relat_1(B_38) = A_37
      | ~ v1_partfun1(B_38,A_37)
      | ~ v4_relat_1(B_38,A_37)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_4285,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_4281,c_54])).

tff(c_4288,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4250,c_4285])).

tff(c_4289,plain,(
    ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_4288])).

tff(c_18,plain,(
    ! [A_8] :
      ( k1_relat_1(k2_funct_1(A_8)) = k2_relat_1(A_8)
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_48,plain,(
    ! [B_35,C_36] :
      ( k1_relset_1(k1_xboole_0,B_35,C_36) = k1_xboole_0
      | ~ v1_funct_2(C_36,k1_xboole_0,B_35)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_91,plain,(
    ! [B_35,C_36] :
      ( k1_relset_1(k1_xboole_0,B_35,C_36) = k1_xboole_0
      | ~ v1_funct_2(C_36,k1_xboole_0,B_35)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_48])).

tff(c_3818,plain,(
    ! [B_552,C_553] :
      ( k1_relset_1('#skF_3',B_552,C_553) = '#skF_3'
      | ~ v1_funct_2(C_553,'#skF_3',B_552)
      | ~ m1_subset_1(C_553,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3474,c_3474,c_3474,c_3474,c_91])).

tff(c_3820,plain,
    ( k1_relset_1('#skF_3',k2_relat_1('#skF_3'),'#skF_3') = '#skF_3'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3775,c_3818])).

tff(c_3826,plain,(
    k1_relset_1('#skF_3',k2_relat_1('#skF_3'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3490,c_3820])).

tff(c_44,plain,(
    ! [C_36,B_35] :
      ( v1_funct_2(C_36,k1_xboole_0,B_35)
      | k1_relset_1(k1_xboole_0,B_35,C_36) != k1_xboole_0
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_92,plain,(
    ! [C_36,B_35] :
      ( v1_funct_2(C_36,k1_xboole_0,B_35)
      | k1_relset_1(k1_xboole_0,B_35,C_36) != k1_xboole_0
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_44])).

tff(c_3836,plain,(
    ! [C_554,B_555] :
      ( v1_funct_2(C_554,'#skF_3',B_555)
      | k1_relset_1('#skF_3',B_555,C_554) != '#skF_3'
      | ~ m1_subset_1(C_554,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3474,c_3474,c_3474,c_3474,c_92])).

tff(c_3840,plain,(
    ! [B_555] :
      ( v1_funct_2('#skF_3','#skF_3',B_555)
      | k1_relset_1('#skF_3',B_555,'#skF_3') != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_3490,c_3836])).

tff(c_4291,plain,(
    ! [B_613] :
      ( v4_relat_1(k2_funct_1('#skF_3'),B_613)
      | k2_relat_1('#skF_3') != B_613
      | k1_relset_1('#skF_3',B_613,'#skF_3') != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_3840,c_4270])).

tff(c_52,plain,(
    ! [B_38] :
      ( v1_partfun1(B_38,k1_relat_1(B_38))
      | ~ v4_relat_1(B_38,k1_relat_1(B_38))
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_4298,plain,
    ( v1_partfun1(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | k1_relat_1(k2_funct_1('#skF_3')) != k2_relat_1('#skF_3')
    | k1_relset_1('#skF_3',k1_relat_1(k2_funct_1('#skF_3')),'#skF_3') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_4291,c_52])).

tff(c_4304,plain,
    ( v1_partfun1(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')))
    | k1_relat_1(k2_funct_1('#skF_3')) != k2_relat_1('#skF_3')
    | k1_relset_1('#skF_3',k1_relat_1(k2_funct_1('#skF_3')),'#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4250,c_4298])).

tff(c_4322,plain,(
    k1_relset_1('#skF_3',k1_relat_1(k2_funct_1('#skF_3')),'#skF_3') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4304])).

tff(c_4343,plain,
    ( k1_relset_1('#skF_3',k2_relat_1('#skF_3'),'#skF_3') != '#skF_3'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_4322])).

tff(c_4346,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3392,c_82,c_74,c_3826,c_4343])).

tff(c_4347,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) != k2_relat_1('#skF_3')
    | v1_partfun1(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_4304])).

tff(c_4369,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_4347])).

tff(c_4381,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_4369])).

tff(c_4385,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3392,c_82,c_74,c_4381])).

tff(c_4387,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_4347])).

tff(c_3679,plain,(
    ! [A_530] :
      ( k1_relat_1(k2_funct_1(A_530)) = k2_relat_1(A_530)
      | ~ v2_funct_1(A_530)
      | ~ v1_funct_1(A_530)
      | ~ v1_relat_1(A_530) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_3685,plain,(
    ! [A_530] :
      ( v1_partfun1(k2_funct_1(A_530),k1_relat_1(k2_funct_1(A_530)))
      | ~ v4_relat_1(k2_funct_1(A_530),k2_relat_1(A_530))
      | ~ v1_relat_1(k2_funct_1(A_530))
      | ~ v2_funct_1(A_530)
      | ~ v1_funct_1(A_530)
      | ~ v1_relat_1(A_530) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3679,c_52])).

tff(c_4394,plain,
    ( v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4387,c_3685])).

tff(c_4407,plain,(
    v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3392,c_82,c_74,c_4250,c_4281,c_4394])).

tff(c_4409,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4289,c_4407])).

tff(c_4410,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_4288])).

tff(c_4698,plain,(
    k2_relat_1('#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4683,c_4410])).

tff(c_4716,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3723,c_4698])).

tff(c_4718,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4081,c_4716])).

tff(c_4720,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4075])).

tff(c_3776,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3766,c_154])).

tff(c_4728,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4720,c_3776])).

tff(c_4733,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3468,c_4728])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:45:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.95/2.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.95/2.36  
% 6.95/2.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.95/2.36  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 6.95/2.36  
% 6.95/2.36  %Foreground sorts:
% 6.95/2.36  
% 6.95/2.36  
% 6.95/2.36  %Background operators:
% 6.95/2.36  
% 6.95/2.36  
% 6.95/2.36  %Foreground operators:
% 6.95/2.36  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.95/2.36  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.95/2.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.95/2.36  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.95/2.36  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.95/2.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.95/2.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.95/2.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.95/2.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.95/2.36  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 6.95/2.36  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.95/2.36  tff('#skF_2', type, '#skF_2': $i).
% 6.95/2.36  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 6.95/2.36  tff('#skF_3', type, '#skF_3': $i).
% 6.95/2.36  tff('#skF_1', type, '#skF_1': $i).
% 6.95/2.36  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.95/2.36  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.95/2.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.95/2.36  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 6.95/2.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.95/2.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.95/2.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.95/2.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.95/2.36  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.95/2.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.95/2.36  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 6.95/2.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.95/2.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.95/2.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.95/2.36  
% 7.37/2.40  tff(f_36, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.37/2.40  tff(f_216, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_2)).
% 7.37/2.40  tff(f_172, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 7.37/2.40  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.37/2.40  tff(f_54, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 7.37/2.40  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.37/2.40  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.37/2.40  tff(f_135, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 7.37/2.40  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.37/2.40  tff(f_152, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_funct_2)).
% 7.37/2.40  tff(f_180, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 7.37/2.40  tff(f_168, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 7.37/2.40  tff(f_192, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 7.37/2.40  tff(f_127, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 7.37/2.40  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 7.37/2.40  tff(f_78, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 7.37/2.40  tff(f_38, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 7.37/2.40  tff(f_89, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_partfun1)).
% 7.37/2.40  tff(c_10, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.37/2.40  tff(c_88, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_216])).
% 7.37/2.40  tff(c_124, plain, (![A_58]: (u1_struct_0(A_58)=k2_struct_0(A_58) | ~l1_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_172])).
% 7.37/2.40  tff(c_132, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_88, c_124])).
% 7.37/2.40  tff(c_84, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_216])).
% 7.37/2.40  tff(c_131, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_84, c_124])).
% 7.37/2.40  tff(c_78, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_216])).
% 7.37/2.40  tff(c_162, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_131, c_78])).
% 7.37/2.40  tff(c_163, plain, (![C_61, A_62, B_63]: (v1_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.37/2.40  tff(c_175, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_162, c_163])).
% 7.37/2.40  tff(c_82, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_216])).
% 7.37/2.40  tff(c_74, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_216])).
% 7.37/2.40  tff(c_16, plain, (![A_8]: (k2_relat_1(k2_funct_1(A_8))=k1_relat_1(A_8) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.37/2.40  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 7.37/2.40  tff(c_1821, plain, (![C_289, A_290, B_291]: (v4_relat_1(C_289, A_290) | ~m1_subset_1(C_289, k1_zfmisc_1(k2_zfmisc_1(A_290, B_291))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.37/2.40  tff(c_1835, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_162, c_1821])).
% 7.37/2.40  tff(c_1963, plain, (![B_317, A_318]: (k1_relat_1(B_317)=A_318 | ~v1_partfun1(B_317, A_318) | ~v4_relat_1(B_317, A_318) | ~v1_relat_1(B_317))), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.37/2.40  tff(c_1966, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1835, c_1963])).
% 7.37/2.40  tff(c_1972, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_175, c_1966])).
% 7.37/2.40  tff(c_2013, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_1972])).
% 7.37/2.40  tff(c_2019, plain, (![A_323, B_324, C_325]: (k2_relset_1(A_323, B_324, C_325)=k2_relat_1(C_325) | ~m1_subset_1(C_325, k1_zfmisc_1(k2_zfmisc_1(A_323, B_324))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.37/2.40  tff(c_2033, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_162, c_2019])).
% 7.37/2.40  tff(c_76, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_216])).
% 7.37/2.40  tff(c_156, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_131, c_76])).
% 7.37/2.40  tff(c_2042, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2033, c_156])).
% 7.37/2.40  tff(c_80, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_216])).
% 7.37/2.40  tff(c_133, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_80])).
% 7.37/2.40  tff(c_161, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_133])).
% 7.37/2.40  tff(c_2053, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2042, c_161])).
% 7.37/2.40  tff(c_2052, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_2042, c_162])).
% 7.37/2.40  tff(c_2156, plain, (![B_340, C_341, A_342]: (k1_xboole_0=B_340 | v1_partfun1(C_341, A_342) | ~v1_funct_2(C_341, A_342, B_340) | ~m1_subset_1(C_341, k1_zfmisc_1(k2_zfmisc_1(A_342, B_340))) | ~v1_funct_1(C_341))), inference(cnfTransformation, [status(thm)], [f_152])).
% 7.37/2.40  tff(c_2159, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2052, c_2156])).
% 7.37/2.40  tff(c_2172, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_2053, c_2159])).
% 7.37/2.40  tff(c_2173, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_2013, c_2172])).
% 7.37/2.40  tff(c_86, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_216])).
% 7.37/2.40  tff(c_143, plain, (![A_60]: (~v1_xboole_0(u1_struct_0(A_60)) | ~l1_struct_0(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_180])).
% 7.37/2.40  tff(c_149, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_131, c_143])).
% 7.37/2.40  tff(c_153, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_149])).
% 7.37/2.40  tff(c_154, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_86, c_153])).
% 7.37/2.40  tff(c_2054, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2042, c_154])).
% 7.37/2.40  tff(c_2183, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2173, c_2054])).
% 7.37/2.40  tff(c_2189, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_2183])).
% 7.37/2.40  tff(c_2190, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_1972])).
% 7.37/2.40  tff(c_2196, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_2190, c_162])).
% 7.37/2.40  tff(c_30, plain, (![A_23, B_24, C_25]: (k2_relset_1(A_23, B_24, C_25)=k2_relat_1(C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.37/2.40  tff(c_2275, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2196, c_30])).
% 7.37/2.40  tff(c_2198, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2190, c_156])).
% 7.37/2.40  tff(c_2287, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2275, c_2198])).
% 7.37/2.40  tff(c_2197, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2190, c_161])).
% 7.37/2.40  tff(c_2294, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2287, c_2197])).
% 7.37/2.40  tff(c_2292, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2287, c_2275])).
% 7.37/2.40  tff(c_2293, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_2287, c_2196])).
% 7.37/2.40  tff(c_2636, plain, (![C_400, B_401, A_402]: (m1_subset_1(k2_funct_1(C_400), k1_zfmisc_1(k2_zfmisc_1(B_401, A_402))) | k2_relset_1(A_402, B_401, C_400)!=B_401 | ~v2_funct_1(C_400) | ~m1_subset_1(C_400, k1_zfmisc_1(k2_zfmisc_1(A_402, B_401))) | ~v1_funct_2(C_400, A_402, B_401) | ~v1_funct_1(C_400))), inference(cnfTransformation, [status(thm)], [f_168])).
% 7.37/2.40  tff(c_3294, plain, (![B_479, A_480, C_481]: (k2_relset_1(B_479, A_480, k2_funct_1(C_481))=k2_relat_1(k2_funct_1(C_481)) | k2_relset_1(A_480, B_479, C_481)!=B_479 | ~v2_funct_1(C_481) | ~m1_subset_1(C_481, k1_zfmisc_1(k2_zfmisc_1(A_480, B_479))) | ~v1_funct_2(C_481, A_480, B_479) | ~v1_funct_1(C_481))), inference(resolution, [status(thm)], [c_2636, c_30])).
% 7.37/2.40  tff(c_3300, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2293, c_3294])).
% 7.37/2.40  tff(c_3314, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_2294, c_74, c_2292, c_3300])).
% 7.37/2.40  tff(c_2595, plain, (![A_393, B_394, C_395]: (k2_tops_2(A_393, B_394, C_395)=k2_funct_1(C_395) | ~v2_funct_1(C_395) | k2_relset_1(A_393, B_394, C_395)!=B_394 | ~m1_subset_1(C_395, k1_zfmisc_1(k2_zfmisc_1(A_393, B_394))) | ~v1_funct_2(C_395, A_393, B_394) | ~v1_funct_1(C_395))), inference(cnfTransformation, [status(thm)], [f_192])).
% 7.37/2.40  tff(c_2598, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2293, c_2595])).
% 7.37/2.40  tff(c_2611, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_2294, c_2292, c_74, c_2598])).
% 7.37/2.40  tff(c_227, plain, (![C_74, A_75, B_76]: (v4_relat_1(C_74, A_75) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.37/2.40  tff(c_241, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_162, c_227])).
% 7.37/2.40  tff(c_363, plain, (![B_103, A_104]: (k1_relat_1(B_103)=A_104 | ~v1_partfun1(B_103, A_104) | ~v4_relat_1(B_103, A_104) | ~v1_relat_1(B_103))), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.37/2.40  tff(c_366, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_241, c_363])).
% 7.37/2.40  tff(c_372, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_175, c_366])).
% 7.37/2.40  tff(c_402, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_372])).
% 7.37/2.40  tff(c_421, plain, (![A_109, B_110, C_111]: (k2_relset_1(A_109, B_110, C_111)=k2_relat_1(C_111) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.37/2.40  tff(c_435, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_162, c_421])).
% 7.37/2.40  tff(c_449, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_435, c_156])).
% 7.37/2.40  tff(c_459, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_449, c_161])).
% 7.37/2.40  tff(c_458, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_449, c_162])).
% 7.37/2.40  tff(c_569, plain, (![B_127, C_128, A_129]: (k1_xboole_0=B_127 | v1_partfun1(C_128, A_129) | ~v1_funct_2(C_128, A_129, B_127) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_129, B_127))) | ~v1_funct_1(C_128))), inference(cnfTransformation, [status(thm)], [f_152])).
% 7.37/2.40  tff(c_572, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_458, c_569])).
% 7.37/2.40  tff(c_585, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_459, c_572])).
% 7.37/2.40  tff(c_586, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_402, c_585])).
% 7.37/2.40  tff(c_460, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_449, c_154])).
% 7.37/2.40  tff(c_596, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_586, c_460])).
% 7.37/2.40  tff(c_602, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_596])).
% 7.37/2.40  tff(c_603, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_372])).
% 7.37/2.40  tff(c_608, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_603, c_162])).
% 7.37/2.40  tff(c_694, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_608, c_30])).
% 7.37/2.40  tff(c_610, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_603, c_156])).
% 7.37/2.40  tff(c_710, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_694, c_610])).
% 7.37/2.40  tff(c_609, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_603, c_161])).
% 7.37/2.40  tff(c_717, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_710, c_609])).
% 7.37/2.40  tff(c_715, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_710, c_694])).
% 7.37/2.40  tff(c_716, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_710, c_608])).
% 7.37/2.40  tff(c_1000, plain, (![A_177, B_178, C_179]: (k2_tops_2(A_177, B_178, C_179)=k2_funct_1(C_179) | ~v2_funct_1(C_179) | k2_relset_1(A_177, B_178, C_179)!=B_178 | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1(A_177, B_178))) | ~v1_funct_2(C_179, A_177, B_178) | ~v1_funct_1(C_179))), inference(cnfTransformation, [status(thm)], [f_192])).
% 7.37/2.40  tff(c_1003, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_716, c_1000])).
% 7.37/2.40  tff(c_1016, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_717, c_715, c_74, c_1003])).
% 7.37/2.40  tff(c_72, plain, (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_216])).
% 7.37/2.40  tff(c_211, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_132, c_131, c_131, c_132, c_132, c_131, c_131, c_72])).
% 7.37/2.40  tff(c_212, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_211])).
% 7.37/2.40  tff(c_606, plain, (k1_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_603, c_603, c_212])).
% 7.37/2.40  tff(c_823, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_710, c_710, c_710, c_606])).
% 7.37/2.40  tff(c_1019, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1016, c_823])).
% 7.37/2.40  tff(c_966, plain, (![C_170, B_171, A_172]: (v1_funct_2(k2_funct_1(C_170), B_171, A_172) | k2_relset_1(A_172, B_171, C_170)!=B_171 | ~v2_funct_1(C_170) | ~m1_subset_1(C_170, k1_zfmisc_1(k2_zfmisc_1(A_172, B_171))) | ~v1_funct_2(C_170, A_172, B_171) | ~v1_funct_1(C_170))), inference(cnfTransformation, [status(thm)], [f_168])).
% 7.37/2.40  tff(c_969, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_716, c_966])).
% 7.37/2.40  tff(c_982, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_717, c_74, c_715, c_969])).
% 7.37/2.40  tff(c_1044, plain, (![C_186, B_187, A_188]: (m1_subset_1(k2_funct_1(C_186), k1_zfmisc_1(k2_zfmisc_1(B_187, A_188))) | k2_relset_1(A_188, B_187, C_186)!=B_187 | ~v2_funct_1(C_186) | ~m1_subset_1(C_186, k1_zfmisc_1(k2_zfmisc_1(A_188, B_187))) | ~v1_funct_2(C_186, A_188, B_187) | ~v1_funct_1(C_186))), inference(cnfTransformation, [status(thm)], [f_168])).
% 7.37/2.40  tff(c_50, plain, (![B_35, A_34, C_36]: (k1_xboole_0=B_35 | k1_relset_1(A_34, B_35, C_36)=A_34 | ~v1_funct_2(C_36, A_34, B_35) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.37/2.40  tff(c_1760, plain, (![A_282, B_283, C_284]: (k1_xboole_0=A_282 | k1_relset_1(B_283, A_282, k2_funct_1(C_284))=B_283 | ~v1_funct_2(k2_funct_1(C_284), B_283, A_282) | k2_relset_1(A_282, B_283, C_284)!=B_283 | ~v2_funct_1(C_284) | ~m1_subset_1(C_284, k1_zfmisc_1(k2_zfmisc_1(A_282, B_283))) | ~v1_funct_2(C_284, A_282, B_283) | ~v1_funct_1(C_284))), inference(resolution, [status(thm)], [c_1044, c_50])).
% 7.37/2.40  tff(c_1766, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_716, c_1760])).
% 7.37/2.40  tff(c_1780, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_717, c_74, c_715, c_982, c_1766])).
% 7.37/2.40  tff(c_1781, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_1019, c_1780])).
% 7.37/2.40  tff(c_146, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_132, c_143])).
% 7.37/2.40  tff(c_151, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_146])).
% 7.37/2.40  tff(c_155, plain, (~v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_151])).
% 7.37/2.40  tff(c_611, plain, (~v1_xboole_0(k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_603, c_155])).
% 7.37/2.40  tff(c_1798, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1781, c_611])).
% 7.37/2.40  tff(c_1804, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_1798])).
% 7.37/2.40  tff(c_1805, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_211])).
% 7.37/2.40  tff(c_2192, plain, (k2_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2190, c_2190, c_2190, c_1805])).
% 7.37/2.40  tff(c_2405, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2287, c_2287, c_2192])).
% 7.37/2.40  tff(c_2615, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2611, c_2405])).
% 7.37/2.40  tff(c_3317, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3314, c_2615])).
% 7.37/2.40  tff(c_3324, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16, c_3317])).
% 7.37/2.40  tff(c_3328, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_175, c_82, c_74, c_3324])).
% 7.37/2.40  tff(c_3330, plain, (v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_151])).
% 7.37/2.40  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 7.37/2.40  tff(c_3334, plain, (k2_struct_0('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_3330, c_4])).
% 7.37/2.40  tff(c_3342, plain, (u1_struct_0('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3334, c_132])).
% 7.37/2.40  tff(c_3358, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_3342, c_131, c_78])).
% 7.37/2.40  tff(c_8, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.37/2.40  tff(c_3444, plain, (![C_499, B_500, A_501]: (v1_xboole_0(C_499) | ~m1_subset_1(C_499, k1_zfmisc_1(k2_zfmisc_1(B_500, A_501))) | ~v1_xboole_0(A_501))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.37/2.40  tff(c_3454, plain, (![C_499]: (v1_xboole_0(C_499) | ~m1_subset_1(C_499, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_3444])).
% 7.37/2.40  tff(c_3460, plain, (![C_503]: (v1_xboole_0(C_503) | ~m1_subset_1(C_503, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_3454])).
% 7.37/2.40  tff(c_3468, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_3358, c_3460])).
% 7.37/2.40  tff(c_3474, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_3468, c_4])).
% 7.37/2.40  tff(c_12, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.37/2.40  tff(c_40, plain, (![A_34]: (v1_funct_2(k1_xboole_0, A_34, k1_xboole_0) | k1_xboole_0=A_34 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_34, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.37/2.40  tff(c_90, plain, (![A_34]: (v1_funct_2(k1_xboole_0, A_34, k1_xboole_0) | k1_xboole_0=A_34)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_40])).
% 7.37/2.40  tff(c_3488, plain, (![A_34]: (v1_funct_2('#skF_3', A_34, '#skF_3') | A_34='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3474, c_3474, c_3474, c_90])).
% 7.37/2.40  tff(c_3490, plain, (![A_4]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_3474, c_12])).
% 7.37/2.40  tff(c_3754, plain, (![A_539, B_540, C_541]: (k2_relset_1(A_539, B_540, C_541)=k2_relat_1(C_541) | ~m1_subset_1(C_541, k1_zfmisc_1(k2_zfmisc_1(A_539, B_540))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.37/2.40  tff(c_3765, plain, (![A_539, B_540]: (k2_relset_1(A_539, B_540, '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_3490, c_3754])).
% 7.37/2.40  tff(c_4044, plain, (![A_589, B_590, C_591]: (k2_tops_2(A_589, B_590, C_591)=k2_funct_1(C_591) | ~v2_funct_1(C_591) | k2_relset_1(A_589, B_590, C_591)!=B_590 | ~m1_subset_1(C_591, k1_zfmisc_1(k2_zfmisc_1(A_589, B_590))) | ~v1_funct_2(C_591, A_589, B_590) | ~v1_funct_1(C_591))), inference(cnfTransformation, [status(thm)], [f_192])).
% 7.37/2.40  tff(c_4048, plain, (![A_589, B_590]: (k2_tops_2(A_589, B_590, '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(A_589, B_590, '#skF_3')!=B_590 | ~v1_funct_2('#skF_3', A_589, B_590) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_3490, c_4044])).
% 7.37/2.40  tff(c_4059, plain, (![A_592, B_593]: (k2_tops_2(A_592, B_593, '#skF_3')=k2_funct_1('#skF_3') | k2_relat_1('#skF_3')!=B_593 | ~v1_funct_2('#skF_3', A_592, B_593))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_3765, c_74, c_4048])).
% 7.37/2.40  tff(c_4075, plain, (![A_34]: (k2_tops_2(A_34, '#skF_3', '#skF_3')=k2_funct_1('#skF_3') | k2_relat_1('#skF_3')!='#skF_3' | A_34='#skF_3')), inference(resolution, [status(thm)], [c_3488, c_4059])).
% 7.37/2.40  tff(c_4081, plain, (k2_relat_1('#skF_3')!='#skF_3'), inference(splitLeft, [status(thm)], [c_4075])).
% 7.37/2.40  tff(c_3700, plain, (![C_532, A_533, B_534]: (v1_partfun1(C_532, A_533) | ~m1_subset_1(C_532, k1_zfmisc_1(k2_zfmisc_1(A_533, B_534))) | ~v1_xboole_0(A_533))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.37/2.40  tff(c_3714, plain, (![A_535]: (v1_partfun1('#skF_3', A_535) | ~v1_xboole_0(A_535))), inference(resolution, [status(thm)], [c_3490, c_3700])).
% 7.37/2.40  tff(c_3374, plain, (![C_484, A_485, B_486]: (v1_relat_1(C_484) | ~m1_subset_1(C_484, k1_zfmisc_1(k2_zfmisc_1(A_485, B_486))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.37/2.40  tff(c_3384, plain, (![C_487]: (v1_relat_1(C_487) | ~m1_subset_1(C_487, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_3374])).
% 7.37/2.40  tff(c_3392, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_3358, c_3384])).
% 7.37/2.40  tff(c_3395, plain, (![C_488, A_489, B_490]: (v4_relat_1(C_488, A_489) | ~m1_subset_1(C_488, k1_zfmisc_1(k2_zfmisc_1(A_489, B_490))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.37/2.40  tff(c_3421, plain, (![C_493, A_494]: (v4_relat_1(C_493, A_494) | ~m1_subset_1(C_493, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_3395])).
% 7.37/2.40  tff(c_3427, plain, (![A_494]: (v4_relat_1('#skF_3', A_494))), inference(resolution, [status(thm)], [c_3358, c_3421])).
% 7.37/2.40  tff(c_3666, plain, (![B_527, A_528]: (k1_relat_1(B_527)=A_528 | ~v1_partfun1(B_527, A_528) | ~v4_relat_1(B_527, A_528) | ~v1_relat_1(B_527))), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.37/2.40  tff(c_3669, plain, (![A_494]: (k1_relat_1('#skF_3')=A_494 | ~v1_partfun1('#skF_3', A_494) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_3427, c_3666])).
% 7.37/2.40  tff(c_3672, plain, (![A_494]: (k1_relat_1('#skF_3')=A_494 | ~v1_partfun1('#skF_3', A_494))), inference(demodulation, [status(thm), theory('equality')], [c_3392, c_3669])).
% 7.37/2.40  tff(c_3719, plain, (![A_536]: (k1_relat_1('#skF_3')=A_536 | ~v1_xboole_0(A_536))), inference(resolution, [status(thm)], [c_3714, c_3672])).
% 7.37/2.40  tff(c_3723, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_3468, c_3719])).
% 7.37/2.40  tff(c_3335, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_131, c_132, c_76])).
% 7.37/2.40  tff(c_3340, plain, (k2_relset_1(k1_xboole_0, k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3334, c_3335])).
% 7.37/2.40  tff(c_3483, plain, (k2_relset_1('#skF_3', k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3474, c_3340])).
% 7.37/2.40  tff(c_3766, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3765, c_3483])).
% 7.37/2.40  tff(c_3357, plain, (v1_funct_2('#skF_3', k1_xboole_0, k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3342, c_133])).
% 7.37/2.40  tff(c_3485, plain, (v1_funct_2('#skF_3', '#skF_3', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3474, c_3357])).
% 7.37/2.40  tff(c_3775, plain, (v1_funct_2('#skF_3', '#skF_3', k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3766, c_3485])).
% 7.37/2.40  tff(c_4082, plain, (![C_594, B_595, A_596]: (m1_subset_1(k2_funct_1(C_594), k1_zfmisc_1(k2_zfmisc_1(B_595, A_596))) | k2_relset_1(A_596, B_595, C_594)!=B_595 | ~v2_funct_1(C_594) | ~m1_subset_1(C_594, k1_zfmisc_1(k2_zfmisc_1(A_596, B_595))) | ~v1_funct_2(C_594, A_596, B_595) | ~v1_funct_1(C_594))), inference(cnfTransformation, [status(thm)], [f_168])).
% 7.37/2.40  tff(c_28, plain, (![C_22, B_20, A_19]: (v1_xboole_0(C_22) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(B_20, A_19))) | ~v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.37/2.40  tff(c_4632, plain, (![C_654, A_655, B_656]: (v1_xboole_0(k2_funct_1(C_654)) | ~v1_xboole_0(A_655) | k2_relset_1(A_655, B_656, C_654)!=B_656 | ~v2_funct_1(C_654) | ~m1_subset_1(C_654, k1_zfmisc_1(k2_zfmisc_1(A_655, B_656))) | ~v1_funct_2(C_654, A_655, B_656) | ~v1_funct_1(C_654))), inference(resolution, [status(thm)], [c_4082, c_28])).
% 7.37/2.40  tff(c_4639, plain, (![A_655, B_656]: (v1_xboole_0(k2_funct_1('#skF_3')) | ~v1_xboole_0(A_655) | k2_relset_1(A_655, B_656, '#skF_3')!=B_656 | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', A_655, B_656) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_3490, c_4632])).
% 7.37/2.40  tff(c_4649, plain, (![A_655, B_656]: (v1_xboole_0(k2_funct_1('#skF_3')) | ~v1_xboole_0(A_655) | k2_relat_1('#skF_3')!=B_656 | ~v1_funct_2('#skF_3', A_655, B_656))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_74, c_3765, c_4639])).
% 7.37/2.40  tff(c_4654, plain, (![A_657, B_658]: (~v1_xboole_0(A_657) | k2_relat_1('#skF_3')!=B_658 | ~v1_funct_2('#skF_3', A_657, B_658))), inference(splitLeft, [status(thm)], [c_4649])).
% 7.37/2.40  tff(c_4663, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_3775, c_4654])).
% 7.37/2.40  tff(c_4674, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3468, c_4663])).
% 7.37/2.40  tff(c_4675, plain, (v1_xboole_0(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_4649])).
% 7.37/2.40  tff(c_3492, plain, (![A_1]: (A_1='#skF_3' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_3474, c_4])).
% 7.37/2.40  tff(c_4683, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_4675, c_3492])).
% 7.37/2.40  tff(c_20, plain, (![C_11, A_9, B_10]: (v1_relat_1(C_11) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.37/2.40  tff(c_4228, plain, (![C_605, A_606, B_607]: (v1_relat_1(k2_funct_1(C_605)) | k2_relset_1(A_606, B_607, C_605)!=B_607 | ~v2_funct_1(C_605) | ~m1_subset_1(C_605, k1_zfmisc_1(k2_zfmisc_1(A_606, B_607))) | ~v1_funct_2(C_605, A_606, B_607) | ~v1_funct_1(C_605))), inference(resolution, [status(thm)], [c_4082, c_20])).
% 7.37/2.40  tff(c_4235, plain, (![A_606, B_607]: (v1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(A_606, B_607, '#skF_3')!=B_607 | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', A_606, B_607) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_3490, c_4228])).
% 7.37/2.40  tff(c_4245, plain, (![B_607, A_606]: (v1_relat_1(k2_funct_1('#skF_3')) | k2_relat_1('#skF_3')!=B_607 | ~v1_funct_2('#skF_3', A_606, B_607))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_74, c_3765, c_4235])).
% 7.37/2.40  tff(c_4247, plain, (![A_606]: (~v1_funct_2('#skF_3', A_606, k2_relat_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_4245])).
% 7.37/2.40  tff(c_4249, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4247, c_3775])).
% 7.37/2.40  tff(c_4250, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_4245])).
% 7.37/2.40  tff(c_24, plain, (![C_14, A_12, B_13]: (v4_relat_1(C_14, A_12) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.37/2.40  tff(c_4251, plain, (![C_608, B_609, A_610]: (v4_relat_1(k2_funct_1(C_608), B_609) | k2_relset_1(A_610, B_609, C_608)!=B_609 | ~v2_funct_1(C_608) | ~m1_subset_1(C_608, k1_zfmisc_1(k2_zfmisc_1(A_610, B_609))) | ~v1_funct_2(C_608, A_610, B_609) | ~v1_funct_1(C_608))), inference(resolution, [status(thm)], [c_4082, c_24])).
% 7.37/2.40  tff(c_4258, plain, (![B_609, A_610]: (v4_relat_1(k2_funct_1('#skF_3'), B_609) | k2_relset_1(A_610, B_609, '#skF_3')!=B_609 | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', A_610, B_609) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_3490, c_4251])).
% 7.37/2.40  tff(c_4270, plain, (![B_611, A_612]: (v4_relat_1(k2_funct_1('#skF_3'), B_611) | k2_relat_1('#skF_3')!=B_611 | ~v1_funct_2('#skF_3', A_612, B_611))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_74, c_3765, c_4258])).
% 7.37/2.40  tff(c_4281, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_3775, c_4270])).
% 7.37/2.40  tff(c_54, plain, (![B_38, A_37]: (k1_relat_1(B_38)=A_37 | ~v1_partfun1(B_38, A_37) | ~v4_relat_1(B_38, A_37) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.37/2.40  tff(c_4285, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_4281, c_54])).
% 7.37/2.40  tff(c_4288, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4250, c_4285])).
% 7.37/2.40  tff(c_4289, plain, (~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_4288])).
% 7.37/2.40  tff(c_18, plain, (![A_8]: (k1_relat_1(k2_funct_1(A_8))=k2_relat_1(A_8) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.37/2.40  tff(c_48, plain, (![B_35, C_36]: (k1_relset_1(k1_xboole_0, B_35, C_36)=k1_xboole_0 | ~v1_funct_2(C_36, k1_xboole_0, B_35) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_35))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.37/2.40  tff(c_91, plain, (![B_35, C_36]: (k1_relset_1(k1_xboole_0, B_35, C_36)=k1_xboole_0 | ~v1_funct_2(C_36, k1_xboole_0, B_35) | ~m1_subset_1(C_36, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_48])).
% 7.37/2.40  tff(c_3818, plain, (![B_552, C_553]: (k1_relset_1('#skF_3', B_552, C_553)='#skF_3' | ~v1_funct_2(C_553, '#skF_3', B_552) | ~m1_subset_1(C_553, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_3474, c_3474, c_3474, c_3474, c_91])).
% 7.37/2.40  tff(c_3820, plain, (k1_relset_1('#skF_3', k2_relat_1('#skF_3'), '#skF_3')='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_3775, c_3818])).
% 7.37/2.40  tff(c_3826, plain, (k1_relset_1('#skF_3', k2_relat_1('#skF_3'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3490, c_3820])).
% 7.37/2.40  tff(c_44, plain, (![C_36, B_35]: (v1_funct_2(C_36, k1_xboole_0, B_35) | k1_relset_1(k1_xboole_0, B_35, C_36)!=k1_xboole_0 | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_35))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.37/2.40  tff(c_92, plain, (![C_36, B_35]: (v1_funct_2(C_36, k1_xboole_0, B_35) | k1_relset_1(k1_xboole_0, B_35, C_36)!=k1_xboole_0 | ~m1_subset_1(C_36, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_44])).
% 7.37/2.40  tff(c_3836, plain, (![C_554, B_555]: (v1_funct_2(C_554, '#skF_3', B_555) | k1_relset_1('#skF_3', B_555, C_554)!='#skF_3' | ~m1_subset_1(C_554, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_3474, c_3474, c_3474, c_3474, c_92])).
% 7.37/2.40  tff(c_3840, plain, (![B_555]: (v1_funct_2('#skF_3', '#skF_3', B_555) | k1_relset_1('#skF_3', B_555, '#skF_3')!='#skF_3')), inference(resolution, [status(thm)], [c_3490, c_3836])).
% 7.37/2.40  tff(c_4291, plain, (![B_613]: (v4_relat_1(k2_funct_1('#skF_3'), B_613) | k2_relat_1('#skF_3')!=B_613 | k1_relset_1('#skF_3', B_613, '#skF_3')!='#skF_3')), inference(resolution, [status(thm)], [c_3840, c_4270])).
% 7.37/2.40  tff(c_52, plain, (![B_38]: (v1_partfun1(B_38, k1_relat_1(B_38)) | ~v4_relat_1(B_38, k1_relat_1(B_38)) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.37/2.40  tff(c_4298, plain, (v1_partfun1(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3')) | k1_relat_1(k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3') | k1_relset_1('#skF_3', k1_relat_1(k2_funct_1('#skF_3')), '#skF_3')!='#skF_3'), inference(resolution, [status(thm)], [c_4291, c_52])).
% 7.37/2.40  tff(c_4304, plain, (v1_partfun1(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3'))) | k1_relat_1(k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3') | k1_relset_1('#skF_3', k1_relat_1(k2_funct_1('#skF_3')), '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4250, c_4298])).
% 7.37/2.40  tff(c_4322, plain, (k1_relset_1('#skF_3', k1_relat_1(k2_funct_1('#skF_3')), '#skF_3')!='#skF_3'), inference(splitLeft, [status(thm)], [c_4304])).
% 7.37/2.40  tff(c_4343, plain, (k1_relset_1('#skF_3', k2_relat_1('#skF_3'), '#skF_3')!='#skF_3' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_18, c_4322])).
% 7.37/2.40  tff(c_4346, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3392, c_82, c_74, c_3826, c_4343])).
% 7.37/2.40  tff(c_4347, plain, (k1_relat_1(k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3') | v1_partfun1(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_4304])).
% 7.37/2.40  tff(c_4369, plain, (k1_relat_1(k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_4347])).
% 7.37/2.40  tff(c_4381, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_18, c_4369])).
% 7.37/2.40  tff(c_4385, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3392, c_82, c_74, c_4381])).
% 7.37/2.40  tff(c_4387, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_4347])).
% 7.37/2.40  tff(c_3679, plain, (![A_530]: (k1_relat_1(k2_funct_1(A_530))=k2_relat_1(A_530) | ~v2_funct_1(A_530) | ~v1_funct_1(A_530) | ~v1_relat_1(A_530))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.37/2.40  tff(c_3685, plain, (![A_530]: (v1_partfun1(k2_funct_1(A_530), k1_relat_1(k2_funct_1(A_530))) | ~v4_relat_1(k2_funct_1(A_530), k2_relat_1(A_530)) | ~v1_relat_1(k2_funct_1(A_530)) | ~v2_funct_1(A_530) | ~v1_funct_1(A_530) | ~v1_relat_1(A_530))), inference(superposition, [status(thm), theory('equality')], [c_3679, c_52])).
% 7.37/2.40  tff(c_4394, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4387, c_3685])).
% 7.37/2.40  tff(c_4407, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3392, c_82, c_74, c_4250, c_4281, c_4394])).
% 7.37/2.40  tff(c_4409, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4289, c_4407])).
% 7.37/2.40  tff(c_4410, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_4288])).
% 7.37/2.40  tff(c_4698, plain, (k2_relat_1('#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4683, c_4410])).
% 7.37/2.40  tff(c_4716, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3723, c_4698])).
% 7.37/2.40  tff(c_4718, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4081, c_4716])).
% 7.37/2.40  tff(c_4720, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_4075])).
% 7.37/2.40  tff(c_3776, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3766, c_154])).
% 7.37/2.40  tff(c_4728, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4720, c_3776])).
% 7.37/2.40  tff(c_4733, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3468, c_4728])).
% 7.37/2.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.37/2.40  
% 7.37/2.40  Inference rules
% 7.37/2.40  ----------------------
% 7.37/2.40  #Ref     : 0
% 7.37/2.40  #Sup     : 942
% 7.37/2.40  #Fact    : 0
% 7.37/2.40  #Define  : 0
% 7.37/2.40  #Split   : 20
% 7.37/2.40  #Chain   : 0
% 7.37/2.40  #Close   : 0
% 7.37/2.40  
% 7.37/2.40  Ordering : KBO
% 7.37/2.40  
% 7.37/2.40  Simplification rules
% 7.37/2.40  ----------------------
% 7.37/2.40  #Subsume      : 238
% 7.37/2.40  #Demod        : 942
% 7.37/2.40  #Tautology    : 356
% 7.37/2.40  #SimpNegUnit  : 28
% 7.37/2.40  #BackRed      : 155
% 7.37/2.40  
% 7.37/2.40  #Partial instantiations: 0
% 7.37/2.40  #Strategies tried      : 1
% 7.37/2.40  
% 7.37/2.40  Timing (in seconds)
% 7.37/2.40  ----------------------
% 7.37/2.40  Preprocessing        : 0.38
% 7.37/2.40  Parsing              : 0.20
% 7.37/2.40  CNF conversion       : 0.03
% 7.37/2.40  Main loop            : 1.18
% 7.37/2.40  Inferencing          : 0.41
% 7.37/2.40  Reduction            : 0.40
% 7.37/2.40  Demodulation         : 0.29
% 7.37/2.40  BG Simplification    : 0.05
% 7.37/2.40  Subsumption          : 0.23
% 7.37/2.40  Abstraction          : 0.06
% 7.37/2.40  MUC search           : 0.00
% 7.37/2.40  Cooper               : 0.00
% 7.37/2.40  Total                : 1.65
% 7.37/2.40  Index Insertion      : 0.00
% 7.37/2.40  Index Deletion       : 0.00
% 7.37/2.40  Index Matching       : 0.00
% 7.37/2.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
