%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:14 EST 2020

% Result     : Theorem 4.58s
% Output     : CNFRefutation 4.76s
% Verified   : 
% Statistics : Number of formulae       :  212 (5151 expanded)
%              Number of leaves         :   53 (1816 expanded)
%              Depth                    :   19
%              Number of atoms          :  362 (15707 expanded)
%              Number of equality atoms :  109 (5143 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k3_tarski > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_197,negated_conjecture,(
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

tff(f_121,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_129,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_117,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_63,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_161,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_173,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_tops_2(A,B,C))
        & v1_funct_2(k2_tops_2(A,B,C),B,A)
        & m1_subset_1(k2_tops_2(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_35,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_149,axiom,(
    ! [A] :
      ( ~ ( ? [B] :
              ( B != k1_xboole_0
              & r2_hidden(B,A) )
          & k3_tarski(A) = k1_xboole_0 )
      & ~ ( k3_tarski(A) != k1_xboole_0
          & ! [B] :
              ~ ( B != k1_xboole_0
                & r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_orders_1)).

tff(f_109,axiom,(
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

tff(f_53,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_relat_1)).

tff(c_88,plain,(
    l1_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_118,plain,(
    ! [A_49] :
      ( u1_struct_0(A_49) = k2_struct_0(A_49)
      | ~ l1_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_125,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_88,c_118])).

tff(c_92,plain,(
    l1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_126,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_118])).

tff(c_82,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_2017,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_126,c_82])).

tff(c_2034,plain,(
    ! [C_358,A_359,B_360] :
      ( v1_relat_1(C_358)
      | ~ m1_subset_1(C_358,k1_zfmisc_1(k2_zfmisc_1(A_359,B_360))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2038,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2017,c_2034])).

tff(c_2113,plain,(
    ! [A_379,B_380,C_381] :
      ( k2_relset_1(A_379,B_380,C_381) = k2_relat_1(C_381)
      | ~ m1_subset_1(C_381,k1_zfmisc_1(k2_zfmisc_1(A_379,B_380))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2117,plain,(
    k2_relset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_5'),'#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2017,c_2113])).

tff(c_80,plain,(
    k2_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6') = k2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_151,plain,(
    k2_relset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_5'),'#skF_6') = k2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_125,c_80])).

tff(c_2118,plain,(
    k2_struct_0('#skF_5') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2117,c_151])).

tff(c_90,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_139,plain,(
    ! [A_52] :
      ( ~ v1_xboole_0(u1_struct_0(A_52))
      | ~ l1_struct_0(A_52)
      | v2_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_145,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_5'))
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_139])).

tff(c_149,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_145])).

tff(c_150,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_149])).

tff(c_2127,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2118,c_150])).

tff(c_2044,plain,(
    ! [C_363,A_364,B_365] :
      ( v4_relat_1(C_363,A_364)
      | ~ m1_subset_1(C_363,k1_zfmisc_1(k2_zfmisc_1(A_364,B_365))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2048,plain,(
    v4_relat_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_2017,c_2044])).

tff(c_2071,plain,(
    ! [B_374,A_375] :
      ( k1_relat_1(B_374) = A_375
      | ~ v1_partfun1(B_374,A_375)
      | ~ v4_relat_1(B_374,A_375)
      | ~ v1_relat_1(B_374) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_2074,plain,
    ( k2_struct_0('#skF_4') = k1_relat_1('#skF_6')
    | ~ v1_partfun1('#skF_6',k2_struct_0('#skF_4'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2048,c_2071])).

tff(c_2077,plain,
    ( k2_struct_0('#skF_4') = k1_relat_1('#skF_6')
    | ~ v1_partfun1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2038,c_2074])).

tff(c_2078,plain,(
    ~ v1_partfun1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_2077])).

tff(c_86,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_84,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_127,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),k2_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_84])).

tff(c_138,plain,(
    v1_funct_2('#skF_6',k2_struct_0('#skF_4'),k2_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_127])).

tff(c_2128,plain,(
    v1_funct_2('#skF_6',k2_struct_0('#skF_4'),k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2118,c_138])).

tff(c_2126,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_relat_1('#skF_6')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2118,c_2017])).

tff(c_2245,plain,(
    ! [C_405,A_406,B_407] :
      ( v1_partfun1(C_405,A_406)
      | ~ v1_funct_2(C_405,A_406,B_407)
      | ~ v1_funct_1(C_405)
      | ~ m1_subset_1(C_405,k1_zfmisc_1(k2_zfmisc_1(A_406,B_407)))
      | v1_xboole_0(B_407) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2248,plain,
    ( v1_partfun1('#skF_6',k2_struct_0('#skF_4'))
    | ~ v1_funct_2('#skF_6',k2_struct_0('#skF_4'),k2_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0(k2_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_2126,c_2245])).

tff(c_2251,plain,
    ( v1_partfun1('#skF_6',k2_struct_0('#skF_4'))
    | v1_xboole_0(k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_2128,c_2248])).

tff(c_2253,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2127,c_2078,c_2251])).

tff(c_2254,plain,(
    k2_struct_0('#skF_4') = k1_relat_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_2077])).

tff(c_172,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_125,c_82])).

tff(c_30,plain,(
    ! [C_14,A_12,B_13] :
      ( v1_relat_1(C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_176,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_172,c_30])).

tff(c_78,plain,(
    v2_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_26,plain,(
    ! [A_11] :
      ( k2_relat_1(k2_funct_1(A_11)) = k1_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1085,plain,(
    ! [A_214,B_215,C_216] :
      ( k2_relset_1(A_214,B_215,C_216) = k2_relat_1(C_216)
      | ~ m1_subset_1(C_216,k1_zfmisc_1(k2_zfmisc_1(A_214,B_215))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1089,plain,(
    k2_relset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_5'),'#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_172,c_1085])).

tff(c_1090,plain,(
    k2_struct_0('#skF_5') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1089,c_151])).

tff(c_1100,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1090,c_150])).

tff(c_1029,plain,(
    ! [C_204,A_205,B_206] :
      ( v4_relat_1(C_204,A_205)
      | ~ m1_subset_1(C_204,k1_zfmisc_1(k2_zfmisc_1(A_205,B_206))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1033,plain,(
    v4_relat_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_172,c_1029])).

tff(c_1044,plain,(
    ! [B_210,A_211] :
      ( k1_relat_1(B_210) = A_211
      | ~ v1_partfun1(B_210,A_211)
      | ~ v4_relat_1(B_210,A_211)
      | ~ v1_relat_1(B_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1047,plain,
    ( k2_struct_0('#skF_4') = k1_relat_1('#skF_6')
    | ~ v1_partfun1('#skF_6',k2_struct_0('#skF_4'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1033,c_1044])).

tff(c_1050,plain,
    ( k2_struct_0('#skF_4') = k1_relat_1('#skF_6')
    | ~ v1_partfun1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_1047])).

tff(c_1051,plain,(
    ~ v1_partfun1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1050])).

tff(c_1101,plain,(
    v1_funct_2('#skF_6',k2_struct_0('#skF_4'),k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1090,c_138])).

tff(c_1099,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_relat_1('#skF_6')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1090,c_172])).

tff(c_1290,plain,(
    ! [C_261,A_262,B_263] :
      ( v1_partfun1(C_261,A_262)
      | ~ v1_funct_2(C_261,A_262,B_263)
      | ~ v1_funct_1(C_261)
      | ~ m1_subset_1(C_261,k1_zfmisc_1(k2_zfmisc_1(A_262,B_263)))
      | v1_xboole_0(B_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1293,plain,
    ( v1_partfun1('#skF_6',k2_struct_0('#skF_4'))
    | ~ v1_funct_2('#skF_6',k2_struct_0('#skF_4'),k2_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0(k2_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_1099,c_1290])).

tff(c_1296,plain,
    ( v1_partfun1('#skF_6',k2_struct_0('#skF_4'))
    | v1_xboole_0(k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1101,c_1293])).

tff(c_1298,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1100,c_1051,c_1296])).

tff(c_1299,plain,(
    k2_struct_0('#skF_4') = k1_relat_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_1050])).

tff(c_1304,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),k2_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1299,c_172])).

tff(c_1396,plain,(
    ! [A_266,B_267,C_268] :
      ( k2_relset_1(A_266,B_267,C_268) = k2_relat_1(C_268)
      | ~ m1_subset_1(C_268,k1_zfmisc_1(k2_zfmisc_1(A_266,B_267))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1400,plain,(
    k2_relset_1(k1_relat_1('#skF_6'),k2_struct_0('#skF_5'),'#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1304,c_1396])).

tff(c_1306,plain,(
    k2_relset_1(k1_relat_1('#skF_6'),k2_struct_0('#skF_5'),'#skF_6') = k2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1299,c_151])).

tff(c_1401,plain,(
    k2_struct_0('#skF_5') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1400,c_1306])).

tff(c_1307,plain,(
    v1_funct_2('#skF_6',k1_relat_1('#skF_6'),k2_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1299,c_138])).

tff(c_1409,plain,(
    v1_funct_2('#skF_6',k1_relat_1('#skF_6'),k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1401,c_1307])).

tff(c_1410,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),k2_relat_1('#skF_6')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1401,c_1304])).

tff(c_1408,plain,(
    k2_relset_1(k1_relat_1('#skF_6'),k2_relat_1('#skF_6'),'#skF_6') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1401,c_1400])).

tff(c_1755,plain,(
    ! [A_337,B_338,C_339] :
      ( k2_tops_2(A_337,B_338,C_339) = k2_funct_1(C_339)
      | ~ v2_funct_1(C_339)
      | k2_relset_1(A_337,B_338,C_339) != B_338
      | ~ m1_subset_1(C_339,k1_zfmisc_1(k2_zfmisc_1(A_337,B_338)))
      | ~ v1_funct_2(C_339,A_337,B_338)
      | ~ v1_funct_1(C_339) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_1761,plain,
    ( k2_tops_2(k1_relat_1('#skF_6'),k2_relat_1('#skF_6'),'#skF_6') = k2_funct_1('#skF_6')
    | ~ v2_funct_1('#skF_6')
    | k2_relset_1(k1_relat_1('#skF_6'),k2_relat_1('#skF_6'),'#skF_6') != k2_relat_1('#skF_6')
    | ~ v1_funct_2('#skF_6',k1_relat_1('#skF_6'),k2_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1410,c_1755])).

tff(c_1765,plain,(
    k2_tops_2(k1_relat_1('#skF_6'),k2_relat_1('#skF_6'),'#skF_6') = k2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1409,c_1408,c_78,c_1761])).

tff(c_70,plain,(
    ! [A_39,B_40,C_41] :
      ( m1_subset_1(k2_tops_2(A_39,B_40,C_41),k1_zfmisc_1(k2_zfmisc_1(B_40,A_39)))
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40)))
      | ~ v1_funct_2(C_41,A_39,B_40)
      | ~ v1_funct_1(C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_1774,plain,
    ( m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_6'),k1_relat_1('#skF_6'))))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),k2_relat_1('#skF_6'))))
    | ~ v1_funct_2('#skF_6',k1_relat_1('#skF_6'),k2_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1765,c_70])).

tff(c_1778,plain,(
    m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_6'),k1_relat_1('#skF_6')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1409,c_1410,c_1774])).

tff(c_36,plain,(
    ! [A_18,B_19,C_20] :
      ( k2_relset_1(A_18,B_19,C_20) = k2_relat_1(C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1854,plain,(
    k2_relset_1(k2_relat_1('#skF_6'),k1_relat_1('#skF_6'),k2_funct_1('#skF_6')) = k2_relat_1(k2_funct_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_1778,c_36])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_267,plain,(
    ! [A_84,B_85,C_86] :
      ( k2_relset_1(A_84,B_85,C_86) = k2_relat_1(C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_271,plain,(
    k2_relset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_5'),'#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_172,c_267])).

tff(c_272,plain,(
    k2_struct_0('#skF_5') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_151])).

tff(c_281,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_150])).

tff(c_200,plain,(
    ! [C_69,A_70,B_71] :
      ( v4_relat_1(C_69,A_70)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_204,plain,(
    v4_relat_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_172,c_200])).

tff(c_246,plain,(
    ! [B_80,A_81] :
      ( k1_relat_1(B_80) = A_81
      | ~ v1_partfun1(B_80,A_81)
      | ~ v4_relat_1(B_80,A_81)
      | ~ v1_relat_1(B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_249,plain,
    ( k2_struct_0('#skF_4') = k1_relat_1('#skF_6')
    | ~ v1_partfun1('#skF_6',k2_struct_0('#skF_4'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_204,c_246])).

tff(c_252,plain,
    ( k2_struct_0('#skF_4') = k1_relat_1('#skF_6')
    | ~ v1_partfun1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_249])).

tff(c_265,plain,(
    ~ v1_partfun1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_252])).

tff(c_282,plain,(
    v1_funct_2('#skF_6',k2_struct_0('#skF_4'),k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_138])).

tff(c_280,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_relat_1('#skF_6')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_172])).

tff(c_404,plain,(
    ! [C_111,A_112,B_113] :
      ( v1_partfun1(C_111,A_112)
      | ~ v1_funct_2(C_111,A_112,B_113)
      | ~ v1_funct_1(C_111)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113)))
      | v1_xboole_0(B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_407,plain,
    ( v1_partfun1('#skF_6',k2_struct_0('#skF_4'))
    | ~ v1_funct_2('#skF_6',k2_struct_0('#skF_4'),k2_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0(k2_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_280,c_404])).

tff(c_410,plain,
    ( v1_partfun1('#skF_6',k2_struct_0('#skF_4'))
    | v1_xboole_0(k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_282,c_407])).

tff(c_412,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_281,c_265,c_410])).

tff(c_413,plain,(
    k2_struct_0('#skF_4') = k1_relat_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_252])).

tff(c_418,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),k2_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_413,c_172])).

tff(c_475,plain,(
    k2_relset_1(k1_relat_1('#skF_6'),k2_struct_0('#skF_5'),'#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_418,c_36])).

tff(c_420,plain,(
    k2_relset_1(k1_relat_1('#skF_6'),k2_struct_0('#skF_5'),'#skF_6') = k2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_413,c_151])).

tff(c_482,plain,(
    k2_struct_0('#skF_5') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_475,c_420])).

tff(c_421,plain,(
    v1_funct_2('#skF_6',k1_relat_1('#skF_6'),k2_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_413,c_138])).

tff(c_489,plain,(
    v1_funct_2('#skF_6',k1_relat_1('#skF_6'),k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_482,c_421])).

tff(c_487,plain,(
    k2_relset_1(k1_relat_1('#skF_6'),k2_relat_1('#skF_6'),'#skF_6') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_482,c_475])).

tff(c_488,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),k2_relat_1('#skF_6')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_482,c_418])).

tff(c_842,plain,(
    ! [A_187,B_188,C_189] :
      ( k2_tops_2(A_187,B_188,C_189) = k2_funct_1(C_189)
      | ~ v2_funct_1(C_189)
      | k2_relset_1(A_187,B_188,C_189) != B_188
      | ~ m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1(A_187,B_188)))
      | ~ v1_funct_2(C_189,A_187,B_188)
      | ~ v1_funct_1(C_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_848,plain,
    ( k2_tops_2(k1_relat_1('#skF_6'),k2_relat_1('#skF_6'),'#skF_6') = k2_funct_1('#skF_6')
    | ~ v2_funct_1('#skF_6')
    | k2_relset_1(k1_relat_1('#skF_6'),k2_relat_1('#skF_6'),'#skF_6') != k2_relat_1('#skF_6')
    | ~ v1_funct_2('#skF_6',k1_relat_1('#skF_6'),k2_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_488,c_842])).

tff(c_852,plain,(
    k2_tops_2(k1_relat_1('#skF_6'),k2_relat_1('#skF_6'),'#skF_6') = k2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_489,c_487,c_78,c_848])).

tff(c_76,plain,
    ( k2_relset_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6')) != k2_struct_0('#skF_4')
    | k1_relset_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6')) != k2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_177,plain,
    ( k2_relset_1(k2_struct_0('#skF_5'),k2_struct_0('#skF_4'),k2_tops_2(k2_struct_0('#skF_4'),k2_struct_0('#skF_5'),'#skF_6')) != k2_struct_0('#skF_4')
    | k1_relset_1(k2_struct_0('#skF_5'),k2_struct_0('#skF_4'),k2_tops_2(k2_struct_0('#skF_4'),k2_struct_0('#skF_5'),'#skF_6')) != k2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_126,c_125,c_125,c_126,c_126,c_125,c_125,c_76])).

tff(c_178,plain,(
    k1_relset_1(k2_struct_0('#skF_5'),k2_struct_0('#skF_4'),k2_tops_2(k2_struct_0('#skF_4'),k2_struct_0('#skF_5'),'#skF_6')) != k2_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_177])).

tff(c_416,plain,(
    k1_relset_1(k2_struct_0('#skF_5'),k1_relat_1('#skF_6'),k2_tops_2(k1_relat_1('#skF_6'),k2_struct_0('#skF_5'),'#skF_6')) != k2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_413,c_413,c_178])).

tff(c_537,plain,(
    k1_relset_1(k2_relat_1('#skF_6'),k1_relat_1('#skF_6'),k2_tops_2(k1_relat_1('#skF_6'),k2_relat_1('#skF_6'),'#skF_6')) != k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_482,c_482,c_482,c_416])).

tff(c_856,plain,(
    k1_relset_1(k2_relat_1('#skF_6'),k1_relat_1('#skF_6'),k2_funct_1('#skF_6')) != k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_852,c_537])).

tff(c_205,plain,(
    ! [B_72,A_73] :
      ( r1_tarski(k1_relat_1(B_72),A_73)
      | ~ v4_relat_1(B_72,A_73)
      | ~ v1_relat_1(B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    ! [A_6] : k3_tarski(k1_zfmisc_1(A_6)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [C_5,A_1] :
      ( r2_hidden(C_5,k1_zfmisc_1(A_1))
      | ~ r1_tarski(C_5,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_179,plain,(
    ! [A_62,B_63] :
      ( k3_tarski(A_62) != k1_xboole_0
      | ~ r2_hidden(B_63,A_62)
      | k1_xboole_0 = B_63 ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_185,plain,(
    ! [A_1,C_5] :
      ( k3_tarski(k1_zfmisc_1(A_1)) != k1_xboole_0
      | k1_xboole_0 = C_5
      | ~ r1_tarski(C_5,A_1) ) ),
    inference(resolution,[status(thm)],[c_6,c_179])).

tff(c_188,plain,(
    ! [A_1,C_5] :
      ( k1_xboole_0 != A_1
      | k1_xboole_0 = C_5
      | ~ r1_tarski(C_5,A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_185])).

tff(c_217,plain,(
    ! [A_77,B_78] :
      ( k1_xboole_0 != A_77
      | k1_relat_1(B_78) = k1_xboole_0
      | ~ v4_relat_1(B_78,A_77)
      | ~ v1_relat_1(B_78) ) ),
    inference(resolution,[status(thm)],[c_205,c_188])).

tff(c_220,plain,
    ( k2_struct_0('#skF_4') != k1_xboole_0
    | k1_relat_1('#skF_6') = k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_204,c_217])).

tff(c_223,plain,
    ( k2_struct_0('#skF_4') != k1_xboole_0
    | k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_220])).

tff(c_224,plain,(
    k2_struct_0('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_223])).

tff(c_415,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_413,c_224])).

tff(c_717,plain,(
    ! [A_170,B_171,C_172] :
      ( v1_funct_2(k2_tops_2(A_170,B_171,C_172),B_171,A_170)
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(A_170,B_171)))
      | ~ v1_funct_2(C_172,A_170,B_171)
      | ~ v1_funct_1(C_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_719,plain,
    ( v1_funct_2(k2_tops_2(k1_relat_1('#skF_6'),k2_relat_1('#skF_6'),'#skF_6'),k2_relat_1('#skF_6'),k1_relat_1('#skF_6'))
    | ~ v1_funct_2('#skF_6',k1_relat_1('#skF_6'),k2_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_488,c_717])).

tff(c_722,plain,(
    v1_funct_2(k2_tops_2(k1_relat_1('#skF_6'),k2_relat_1('#skF_6'),'#skF_6'),k2_relat_1('#skF_6'),k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_489,c_719])).

tff(c_854,plain,(
    v1_funct_2(k2_funct_1('#skF_6'),k2_relat_1('#skF_6'),k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_852,c_722])).

tff(c_860,plain,
    ( m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_6'),k1_relat_1('#skF_6'))))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),k2_relat_1('#skF_6'))))
    | ~ v1_funct_2('#skF_6',k1_relat_1('#skF_6'),k2_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_852,c_70])).

tff(c_864,plain,(
    m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_6'),k1_relat_1('#skF_6')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_489,c_488,c_860])).

tff(c_52,plain,(
    ! [B_26,A_25,C_27] :
      ( k1_xboole_0 = B_26
      | k1_relset_1(A_25,B_26,C_27) = A_25
      | ~ v1_funct_2(C_27,A_25,B_26)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_916,plain,
    ( k1_relat_1('#skF_6') = k1_xboole_0
    | k1_relset_1(k2_relat_1('#skF_6'),k1_relat_1('#skF_6'),k2_funct_1('#skF_6')) = k2_relat_1('#skF_6')
    | ~ v1_funct_2(k2_funct_1('#skF_6'),k2_relat_1('#skF_6'),k1_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_864,c_52])).

tff(c_953,plain,
    ( k1_relat_1('#skF_6') = k1_xboole_0
    | k1_relset_1(k2_relat_1('#skF_6'),k1_relat_1('#skF_6'),k2_funct_1('#skF_6')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_854,c_916])).

tff(c_955,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_856,c_415,c_953])).

tff(c_957,plain,(
    k2_struct_0('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_223])).

tff(c_142,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_139])).

tff(c_147,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_142])).

tff(c_156,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_147])).

tff(c_985,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_957,c_156])).

tff(c_991,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_985])).

tff(c_992,plain,(
    k2_relset_1(k2_struct_0('#skF_5'),k2_struct_0('#skF_4'),k2_tops_2(k2_struct_0('#skF_4'),k2_struct_0('#skF_5'),'#skF_6')) != k2_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_177])).

tff(c_1406,plain,(
    k2_relset_1(k2_struct_0('#skF_5'),k1_relat_1('#skF_6'),k2_tops_2(k1_relat_1('#skF_6'),k2_struct_0('#skF_5'),'#skF_6')) != k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1299,c_1299,c_1299,c_992])).

tff(c_1407,plain,(
    k2_relset_1(k2_relat_1('#skF_6'),k1_relat_1('#skF_6'),k2_tops_2(k1_relat_1('#skF_6'),k2_relat_1('#skF_6'),'#skF_6')) != k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1401,c_1401,c_1406])).

tff(c_1769,plain,(
    k2_relset_1(k2_relat_1('#skF_6'),k1_relat_1('#skF_6'),k2_funct_1('#skF_6')) != k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1765,c_1407])).

tff(c_1989,plain,(
    k2_relat_1(k2_funct_1('#skF_6')) != k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1854,c_1769])).

tff(c_1996,plain,
    ( ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1989])).

tff(c_2000,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_86,c_78,c_1996])).

tff(c_2002,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_147])).

tff(c_2259,plain,(
    v1_xboole_0(k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2254,c_2002])).

tff(c_24,plain,(
    ! [A_10] :
      ( ~ v1_xboole_0(k1_relat_1(A_10))
      | ~ v1_relat_1(A_10)
      | v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2269,plain,
    ( ~ v1_relat_1('#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_2259,c_24])).

tff(c_2272,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2038,c_2269])).

tff(c_22,plain,(
    ! [A_9] :
      ( v1_xboole_0(k2_relat_1(A_9))
      | ~ v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2258,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),k2_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2254,c_2017])).

tff(c_2356,plain,(
    ! [A_411,B_412,C_413] :
      ( k2_relset_1(A_411,B_412,C_413) = k2_relat_1(C_413)
      | ~ m1_subset_1(C_413,k1_zfmisc_1(k2_zfmisc_1(A_411,B_412))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2360,plain,(
    k2_relset_1(k1_relat_1('#skF_6'),k2_struct_0('#skF_5'),'#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2258,c_2356])).

tff(c_2260,plain,(
    k2_relset_1(k1_relat_1('#skF_6'),k2_struct_0('#skF_5'),'#skF_6') = k2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2254,c_151])).

tff(c_2361,plain,(
    k2_struct_0('#skF_5') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2360,c_2260])).

tff(c_2371,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2361,c_150])).

tff(c_2379,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_22,c_2371])).

tff(c_2383,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2272,c_2379])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:18:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.58/1.80  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.71/1.82  
% 4.71/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.71/1.82  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k3_tarski > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 4.71/1.82  
% 4.71/1.82  %Foreground sorts:
% 4.71/1.82  
% 4.71/1.82  
% 4.71/1.82  %Background operators:
% 4.71/1.82  
% 4.71/1.82  
% 4.71/1.82  %Foreground operators:
% 4.71/1.82  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.71/1.82  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.71/1.82  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.71/1.82  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.71/1.82  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.71/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.71/1.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.71/1.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.71/1.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.71/1.82  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.71/1.82  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 4.71/1.82  tff('#skF_5', type, '#skF_5': $i).
% 4.71/1.82  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.71/1.82  tff('#skF_6', type, '#skF_6': $i).
% 4.71/1.82  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.71/1.82  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.71/1.82  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.71/1.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.71/1.82  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.71/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.71/1.82  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.71/1.82  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.71/1.82  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.71/1.82  tff('#skF_4', type, '#skF_4': $i).
% 4.71/1.82  tff('#skF_3', type, '#skF_3': $i > $i).
% 4.71/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.71/1.82  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.71/1.82  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.71/1.82  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.71/1.82  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.71/1.82  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.71/1.82  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.71/1.82  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.71/1.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.71/1.82  
% 4.76/1.85  tff(f_197, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_2)).
% 4.76/1.85  tff(f_121, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 4.76/1.85  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.76/1.85  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.76/1.85  tff(f_129, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.76/1.85  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.76/1.85  tff(f_117, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 4.76/1.85  tff(f_91, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 4.76/1.85  tff(f_63, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 4.76/1.85  tff(f_161, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 4.76/1.85  tff(f_173, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v1_funct_1(k2_tops_2(A, B, C)) & v1_funct_2(k2_tops_2(A, B, C), B, A)) & m1_subset_1(k2_tops_2(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_2)).
% 4.76/1.85  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.76/1.85  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 4.76/1.85  tff(f_35, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 4.76/1.85  tff(f_33, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 4.76/1.85  tff(f_149, axiom, (![A]: (~((?[B]: (~(B = k1_xboole_0) & r2_hidden(B, A))) & (k3_tarski(A) = k1_xboole_0)) & ~(~(k3_tarski(A) = k1_xboole_0) & (![B]: ~(~(B = k1_xboole_0) & r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_orders_1)).
% 4.76/1.85  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.76/1.85  tff(f_53, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_relat_1)).
% 4.76/1.85  tff(f_45, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc11_relat_1)).
% 4.76/1.85  tff(c_88, plain, (l1_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_197])).
% 4.76/1.85  tff(c_118, plain, (![A_49]: (u1_struct_0(A_49)=k2_struct_0(A_49) | ~l1_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.76/1.85  tff(c_125, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_88, c_118])).
% 4.76/1.85  tff(c_92, plain, (l1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_197])).
% 4.76/1.85  tff(c_126, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_92, c_118])).
% 4.76/1.85  tff(c_82, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_197])).
% 4.76/1.85  tff(c_2017, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_126, c_82])).
% 4.76/1.85  tff(c_2034, plain, (![C_358, A_359, B_360]: (v1_relat_1(C_358) | ~m1_subset_1(C_358, k1_zfmisc_1(k2_zfmisc_1(A_359, B_360))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.76/1.85  tff(c_2038, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2017, c_2034])).
% 4.76/1.85  tff(c_2113, plain, (![A_379, B_380, C_381]: (k2_relset_1(A_379, B_380, C_381)=k2_relat_1(C_381) | ~m1_subset_1(C_381, k1_zfmisc_1(k2_zfmisc_1(A_379, B_380))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.76/1.85  tff(c_2117, plain, (k2_relset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_5'), '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2017, c_2113])).
% 4.76/1.85  tff(c_80, plain, (k2_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')=k2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_197])).
% 4.76/1.85  tff(c_151, plain, (k2_relset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_5'), '#skF_6')=k2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_125, c_80])).
% 4.76/1.85  tff(c_2118, plain, (k2_struct_0('#skF_5')=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2117, c_151])).
% 4.76/1.85  tff(c_90, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_197])).
% 4.76/1.85  tff(c_139, plain, (![A_52]: (~v1_xboole_0(u1_struct_0(A_52)) | ~l1_struct_0(A_52) | v2_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.76/1.85  tff(c_145, plain, (~v1_xboole_0(k2_struct_0('#skF_5')) | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_125, c_139])).
% 4.76/1.85  tff(c_149, plain, (~v1_xboole_0(k2_struct_0('#skF_5')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_145])).
% 4.76/1.85  tff(c_150, plain, (~v1_xboole_0(k2_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_90, c_149])).
% 4.76/1.85  tff(c_2127, plain, (~v1_xboole_0(k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2118, c_150])).
% 4.76/1.85  tff(c_2044, plain, (![C_363, A_364, B_365]: (v4_relat_1(C_363, A_364) | ~m1_subset_1(C_363, k1_zfmisc_1(k2_zfmisc_1(A_364, B_365))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.76/1.85  tff(c_2048, plain, (v4_relat_1('#skF_6', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_2017, c_2044])).
% 4.76/1.85  tff(c_2071, plain, (![B_374, A_375]: (k1_relat_1(B_374)=A_375 | ~v1_partfun1(B_374, A_375) | ~v4_relat_1(B_374, A_375) | ~v1_relat_1(B_374))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.76/1.85  tff(c_2074, plain, (k2_struct_0('#skF_4')=k1_relat_1('#skF_6') | ~v1_partfun1('#skF_6', k2_struct_0('#skF_4')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2048, c_2071])).
% 4.76/1.85  tff(c_2077, plain, (k2_struct_0('#skF_4')=k1_relat_1('#skF_6') | ~v1_partfun1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2038, c_2074])).
% 4.76/1.85  tff(c_2078, plain, (~v1_partfun1('#skF_6', k2_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_2077])).
% 4.76/1.85  tff(c_86, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_197])).
% 4.76/1.85  tff(c_84, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_197])).
% 4.76/1.85  tff(c_127, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), k2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_84])).
% 4.76/1.85  tff(c_138, plain, (v1_funct_2('#skF_6', k2_struct_0('#skF_4'), k2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_127])).
% 4.76/1.85  tff(c_2128, plain, (v1_funct_2('#skF_6', k2_struct_0('#skF_4'), k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2118, c_138])).
% 4.76/1.85  tff(c_2126, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_relat_1('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_2118, c_2017])).
% 4.76/1.85  tff(c_2245, plain, (![C_405, A_406, B_407]: (v1_partfun1(C_405, A_406) | ~v1_funct_2(C_405, A_406, B_407) | ~v1_funct_1(C_405) | ~m1_subset_1(C_405, k1_zfmisc_1(k2_zfmisc_1(A_406, B_407))) | v1_xboole_0(B_407))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.76/1.85  tff(c_2248, plain, (v1_partfun1('#skF_6', k2_struct_0('#skF_4')) | ~v1_funct_2('#skF_6', k2_struct_0('#skF_4'), k2_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | v1_xboole_0(k2_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_2126, c_2245])).
% 4.76/1.85  tff(c_2251, plain, (v1_partfun1('#skF_6', k2_struct_0('#skF_4')) | v1_xboole_0(k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_2128, c_2248])).
% 4.76/1.85  tff(c_2253, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2127, c_2078, c_2251])).
% 4.76/1.85  tff(c_2254, plain, (k2_struct_0('#skF_4')=k1_relat_1('#skF_6')), inference(splitRight, [status(thm)], [c_2077])).
% 4.76/1.85  tff(c_172, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_125, c_82])).
% 4.76/1.85  tff(c_30, plain, (![C_14, A_12, B_13]: (v1_relat_1(C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.76/1.85  tff(c_176, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_172, c_30])).
% 4.76/1.85  tff(c_78, plain, (v2_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_197])).
% 4.76/1.85  tff(c_26, plain, (![A_11]: (k2_relat_1(k2_funct_1(A_11))=k1_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.76/1.85  tff(c_1085, plain, (![A_214, B_215, C_216]: (k2_relset_1(A_214, B_215, C_216)=k2_relat_1(C_216) | ~m1_subset_1(C_216, k1_zfmisc_1(k2_zfmisc_1(A_214, B_215))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.76/1.85  tff(c_1089, plain, (k2_relset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_5'), '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_172, c_1085])).
% 4.76/1.85  tff(c_1090, plain, (k2_struct_0('#skF_5')=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1089, c_151])).
% 4.76/1.85  tff(c_1100, plain, (~v1_xboole_0(k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1090, c_150])).
% 4.76/1.85  tff(c_1029, plain, (![C_204, A_205, B_206]: (v4_relat_1(C_204, A_205) | ~m1_subset_1(C_204, k1_zfmisc_1(k2_zfmisc_1(A_205, B_206))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.76/1.85  tff(c_1033, plain, (v4_relat_1('#skF_6', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_172, c_1029])).
% 4.76/1.85  tff(c_1044, plain, (![B_210, A_211]: (k1_relat_1(B_210)=A_211 | ~v1_partfun1(B_210, A_211) | ~v4_relat_1(B_210, A_211) | ~v1_relat_1(B_210))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.76/1.85  tff(c_1047, plain, (k2_struct_0('#skF_4')=k1_relat_1('#skF_6') | ~v1_partfun1('#skF_6', k2_struct_0('#skF_4')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_1033, c_1044])).
% 4.76/1.85  tff(c_1050, plain, (k2_struct_0('#skF_4')=k1_relat_1('#skF_6') | ~v1_partfun1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_176, c_1047])).
% 4.76/1.85  tff(c_1051, plain, (~v1_partfun1('#skF_6', k2_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_1050])).
% 4.76/1.85  tff(c_1101, plain, (v1_funct_2('#skF_6', k2_struct_0('#skF_4'), k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1090, c_138])).
% 4.76/1.85  tff(c_1099, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_relat_1('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_1090, c_172])).
% 4.76/1.85  tff(c_1290, plain, (![C_261, A_262, B_263]: (v1_partfun1(C_261, A_262) | ~v1_funct_2(C_261, A_262, B_263) | ~v1_funct_1(C_261) | ~m1_subset_1(C_261, k1_zfmisc_1(k2_zfmisc_1(A_262, B_263))) | v1_xboole_0(B_263))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.76/1.85  tff(c_1293, plain, (v1_partfun1('#skF_6', k2_struct_0('#skF_4')) | ~v1_funct_2('#skF_6', k2_struct_0('#skF_4'), k2_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | v1_xboole_0(k2_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_1099, c_1290])).
% 4.76/1.85  tff(c_1296, plain, (v1_partfun1('#skF_6', k2_struct_0('#skF_4')) | v1_xboole_0(k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1101, c_1293])).
% 4.76/1.85  tff(c_1298, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1100, c_1051, c_1296])).
% 4.76/1.85  tff(c_1299, plain, (k2_struct_0('#skF_4')=k1_relat_1('#skF_6')), inference(splitRight, [status(thm)], [c_1050])).
% 4.76/1.85  tff(c_1304, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_1299, c_172])).
% 4.76/1.85  tff(c_1396, plain, (![A_266, B_267, C_268]: (k2_relset_1(A_266, B_267, C_268)=k2_relat_1(C_268) | ~m1_subset_1(C_268, k1_zfmisc_1(k2_zfmisc_1(A_266, B_267))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.76/1.85  tff(c_1400, plain, (k2_relset_1(k1_relat_1('#skF_6'), k2_struct_0('#skF_5'), '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_1304, c_1396])).
% 4.76/1.85  tff(c_1306, plain, (k2_relset_1(k1_relat_1('#skF_6'), k2_struct_0('#skF_5'), '#skF_6')=k2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1299, c_151])).
% 4.76/1.85  tff(c_1401, plain, (k2_struct_0('#skF_5')=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1400, c_1306])).
% 4.76/1.85  tff(c_1307, plain, (v1_funct_2('#skF_6', k1_relat_1('#skF_6'), k2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1299, c_138])).
% 4.76/1.85  tff(c_1409, plain, (v1_funct_2('#skF_6', k1_relat_1('#skF_6'), k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1401, c_1307])).
% 4.76/1.85  tff(c_1410, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), k2_relat_1('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_1401, c_1304])).
% 4.76/1.85  tff(c_1408, plain, (k2_relset_1(k1_relat_1('#skF_6'), k2_relat_1('#skF_6'), '#skF_6')=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1401, c_1400])).
% 4.76/1.85  tff(c_1755, plain, (![A_337, B_338, C_339]: (k2_tops_2(A_337, B_338, C_339)=k2_funct_1(C_339) | ~v2_funct_1(C_339) | k2_relset_1(A_337, B_338, C_339)!=B_338 | ~m1_subset_1(C_339, k1_zfmisc_1(k2_zfmisc_1(A_337, B_338))) | ~v1_funct_2(C_339, A_337, B_338) | ~v1_funct_1(C_339))), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.76/1.85  tff(c_1761, plain, (k2_tops_2(k1_relat_1('#skF_6'), k2_relat_1('#skF_6'), '#skF_6')=k2_funct_1('#skF_6') | ~v2_funct_1('#skF_6') | k2_relset_1(k1_relat_1('#skF_6'), k2_relat_1('#skF_6'), '#skF_6')!=k2_relat_1('#skF_6') | ~v1_funct_2('#skF_6', k1_relat_1('#skF_6'), k2_relat_1('#skF_6')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_1410, c_1755])).
% 4.76/1.85  tff(c_1765, plain, (k2_tops_2(k1_relat_1('#skF_6'), k2_relat_1('#skF_6'), '#skF_6')=k2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1409, c_1408, c_78, c_1761])).
% 4.76/1.85  tff(c_70, plain, (![A_39, B_40, C_41]: (m1_subset_1(k2_tops_2(A_39, B_40, C_41), k1_zfmisc_1(k2_zfmisc_1(B_40, A_39))) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))) | ~v1_funct_2(C_41, A_39, B_40) | ~v1_funct_1(C_41))), inference(cnfTransformation, [status(thm)], [f_173])).
% 4.76/1.85  tff(c_1774, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_6'), k1_relat_1('#skF_6')))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), k2_relat_1('#skF_6')))) | ~v1_funct_2('#skF_6', k1_relat_1('#skF_6'), k2_relat_1('#skF_6')) | ~v1_funct_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1765, c_70])).
% 4.76/1.85  tff(c_1778, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_6'), k1_relat_1('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1409, c_1410, c_1774])).
% 4.76/1.85  tff(c_36, plain, (![A_18, B_19, C_20]: (k2_relset_1(A_18, B_19, C_20)=k2_relat_1(C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.76/1.85  tff(c_1854, plain, (k2_relset_1(k2_relat_1('#skF_6'), k1_relat_1('#skF_6'), k2_funct_1('#skF_6'))=k2_relat_1(k2_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_1778, c_36])).
% 4.76/1.85  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.76/1.85  tff(c_267, plain, (![A_84, B_85, C_86]: (k2_relset_1(A_84, B_85, C_86)=k2_relat_1(C_86) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.76/1.85  tff(c_271, plain, (k2_relset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_5'), '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_172, c_267])).
% 4.76/1.85  tff(c_272, plain, (k2_struct_0('#skF_5')=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_271, c_151])).
% 4.76/1.85  tff(c_281, plain, (~v1_xboole_0(k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_272, c_150])).
% 4.76/1.85  tff(c_200, plain, (![C_69, A_70, B_71]: (v4_relat_1(C_69, A_70) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.76/1.85  tff(c_204, plain, (v4_relat_1('#skF_6', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_172, c_200])).
% 4.76/1.85  tff(c_246, plain, (![B_80, A_81]: (k1_relat_1(B_80)=A_81 | ~v1_partfun1(B_80, A_81) | ~v4_relat_1(B_80, A_81) | ~v1_relat_1(B_80))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.76/1.85  tff(c_249, plain, (k2_struct_0('#skF_4')=k1_relat_1('#skF_6') | ~v1_partfun1('#skF_6', k2_struct_0('#skF_4')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_204, c_246])).
% 4.76/1.85  tff(c_252, plain, (k2_struct_0('#skF_4')=k1_relat_1('#skF_6') | ~v1_partfun1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_176, c_249])).
% 4.76/1.85  tff(c_265, plain, (~v1_partfun1('#skF_6', k2_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_252])).
% 4.76/1.85  tff(c_282, plain, (v1_funct_2('#skF_6', k2_struct_0('#skF_4'), k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_272, c_138])).
% 4.76/1.85  tff(c_280, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_relat_1('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_272, c_172])).
% 4.76/1.85  tff(c_404, plain, (![C_111, A_112, B_113]: (v1_partfun1(C_111, A_112) | ~v1_funct_2(C_111, A_112, B_113) | ~v1_funct_1(C_111) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))) | v1_xboole_0(B_113))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.76/1.85  tff(c_407, plain, (v1_partfun1('#skF_6', k2_struct_0('#skF_4')) | ~v1_funct_2('#skF_6', k2_struct_0('#skF_4'), k2_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | v1_xboole_0(k2_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_280, c_404])).
% 4.76/1.85  tff(c_410, plain, (v1_partfun1('#skF_6', k2_struct_0('#skF_4')) | v1_xboole_0(k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_282, c_407])).
% 4.76/1.85  tff(c_412, plain, $false, inference(negUnitSimplification, [status(thm)], [c_281, c_265, c_410])).
% 4.76/1.85  tff(c_413, plain, (k2_struct_0('#skF_4')=k1_relat_1('#skF_6')), inference(splitRight, [status(thm)], [c_252])).
% 4.76/1.85  tff(c_418, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_413, c_172])).
% 4.76/1.85  tff(c_475, plain, (k2_relset_1(k1_relat_1('#skF_6'), k2_struct_0('#skF_5'), '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_418, c_36])).
% 4.76/1.85  tff(c_420, plain, (k2_relset_1(k1_relat_1('#skF_6'), k2_struct_0('#skF_5'), '#skF_6')=k2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_413, c_151])).
% 4.76/1.85  tff(c_482, plain, (k2_struct_0('#skF_5')=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_475, c_420])).
% 4.76/1.85  tff(c_421, plain, (v1_funct_2('#skF_6', k1_relat_1('#skF_6'), k2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_413, c_138])).
% 4.76/1.85  tff(c_489, plain, (v1_funct_2('#skF_6', k1_relat_1('#skF_6'), k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_482, c_421])).
% 4.76/1.85  tff(c_487, plain, (k2_relset_1(k1_relat_1('#skF_6'), k2_relat_1('#skF_6'), '#skF_6')=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_482, c_475])).
% 4.76/1.85  tff(c_488, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), k2_relat_1('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_482, c_418])).
% 4.76/1.85  tff(c_842, plain, (![A_187, B_188, C_189]: (k2_tops_2(A_187, B_188, C_189)=k2_funct_1(C_189) | ~v2_funct_1(C_189) | k2_relset_1(A_187, B_188, C_189)!=B_188 | ~m1_subset_1(C_189, k1_zfmisc_1(k2_zfmisc_1(A_187, B_188))) | ~v1_funct_2(C_189, A_187, B_188) | ~v1_funct_1(C_189))), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.76/1.85  tff(c_848, plain, (k2_tops_2(k1_relat_1('#skF_6'), k2_relat_1('#skF_6'), '#skF_6')=k2_funct_1('#skF_6') | ~v2_funct_1('#skF_6') | k2_relset_1(k1_relat_1('#skF_6'), k2_relat_1('#skF_6'), '#skF_6')!=k2_relat_1('#skF_6') | ~v1_funct_2('#skF_6', k1_relat_1('#skF_6'), k2_relat_1('#skF_6')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_488, c_842])).
% 4.76/1.85  tff(c_852, plain, (k2_tops_2(k1_relat_1('#skF_6'), k2_relat_1('#skF_6'), '#skF_6')=k2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_489, c_487, c_78, c_848])).
% 4.76/1.85  tff(c_76, plain, (k2_relset_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'))!=k2_struct_0('#skF_4') | k1_relset_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'))!=k2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_197])).
% 4.76/1.85  tff(c_177, plain, (k2_relset_1(k2_struct_0('#skF_5'), k2_struct_0('#skF_4'), k2_tops_2(k2_struct_0('#skF_4'), k2_struct_0('#skF_5'), '#skF_6'))!=k2_struct_0('#skF_4') | k1_relset_1(k2_struct_0('#skF_5'), k2_struct_0('#skF_4'), k2_tops_2(k2_struct_0('#skF_4'), k2_struct_0('#skF_5'), '#skF_6'))!=k2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_126, c_125, c_125, c_126, c_126, c_125, c_125, c_76])).
% 4.76/1.85  tff(c_178, plain, (k1_relset_1(k2_struct_0('#skF_5'), k2_struct_0('#skF_4'), k2_tops_2(k2_struct_0('#skF_4'), k2_struct_0('#skF_5'), '#skF_6'))!=k2_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_177])).
% 4.76/1.85  tff(c_416, plain, (k1_relset_1(k2_struct_0('#skF_5'), k1_relat_1('#skF_6'), k2_tops_2(k1_relat_1('#skF_6'), k2_struct_0('#skF_5'), '#skF_6'))!=k2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_413, c_413, c_178])).
% 4.76/1.85  tff(c_537, plain, (k1_relset_1(k2_relat_1('#skF_6'), k1_relat_1('#skF_6'), k2_tops_2(k1_relat_1('#skF_6'), k2_relat_1('#skF_6'), '#skF_6'))!=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_482, c_482, c_482, c_416])).
% 4.76/1.85  tff(c_856, plain, (k1_relset_1(k2_relat_1('#skF_6'), k1_relat_1('#skF_6'), k2_funct_1('#skF_6'))!=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_852, c_537])).
% 4.76/1.85  tff(c_205, plain, (![B_72, A_73]: (r1_tarski(k1_relat_1(B_72), A_73) | ~v4_relat_1(B_72, A_73) | ~v1_relat_1(B_72))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.76/1.85  tff(c_16, plain, (![A_6]: (k3_tarski(k1_zfmisc_1(A_6))=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.76/1.85  tff(c_6, plain, (![C_5, A_1]: (r2_hidden(C_5, k1_zfmisc_1(A_1)) | ~r1_tarski(C_5, A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.76/1.85  tff(c_179, plain, (![A_62, B_63]: (k3_tarski(A_62)!=k1_xboole_0 | ~r2_hidden(B_63, A_62) | k1_xboole_0=B_63)), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.76/1.85  tff(c_185, plain, (![A_1, C_5]: (k3_tarski(k1_zfmisc_1(A_1))!=k1_xboole_0 | k1_xboole_0=C_5 | ~r1_tarski(C_5, A_1))), inference(resolution, [status(thm)], [c_6, c_179])).
% 4.76/1.85  tff(c_188, plain, (![A_1, C_5]: (k1_xboole_0!=A_1 | k1_xboole_0=C_5 | ~r1_tarski(C_5, A_1))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_185])).
% 4.76/1.85  tff(c_217, plain, (![A_77, B_78]: (k1_xboole_0!=A_77 | k1_relat_1(B_78)=k1_xboole_0 | ~v4_relat_1(B_78, A_77) | ~v1_relat_1(B_78))), inference(resolution, [status(thm)], [c_205, c_188])).
% 4.76/1.85  tff(c_220, plain, (k2_struct_0('#skF_4')!=k1_xboole_0 | k1_relat_1('#skF_6')=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_204, c_217])).
% 4.76/1.85  tff(c_223, plain, (k2_struct_0('#skF_4')!=k1_xboole_0 | k1_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_176, c_220])).
% 4.76/1.85  tff(c_224, plain, (k2_struct_0('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_223])).
% 4.76/1.85  tff(c_415, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_413, c_224])).
% 4.76/1.85  tff(c_717, plain, (![A_170, B_171, C_172]: (v1_funct_2(k2_tops_2(A_170, B_171, C_172), B_171, A_170) | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(A_170, B_171))) | ~v1_funct_2(C_172, A_170, B_171) | ~v1_funct_1(C_172))), inference(cnfTransformation, [status(thm)], [f_173])).
% 4.76/1.85  tff(c_719, plain, (v1_funct_2(k2_tops_2(k1_relat_1('#skF_6'), k2_relat_1('#skF_6'), '#skF_6'), k2_relat_1('#skF_6'), k1_relat_1('#skF_6')) | ~v1_funct_2('#skF_6', k1_relat_1('#skF_6'), k2_relat_1('#skF_6')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_488, c_717])).
% 4.76/1.85  tff(c_722, plain, (v1_funct_2(k2_tops_2(k1_relat_1('#skF_6'), k2_relat_1('#skF_6'), '#skF_6'), k2_relat_1('#skF_6'), k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_489, c_719])).
% 4.76/1.85  tff(c_854, plain, (v1_funct_2(k2_funct_1('#skF_6'), k2_relat_1('#skF_6'), k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_852, c_722])).
% 4.76/1.85  tff(c_860, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_6'), k1_relat_1('#skF_6')))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), k2_relat_1('#skF_6')))) | ~v1_funct_2('#skF_6', k1_relat_1('#skF_6'), k2_relat_1('#skF_6')) | ~v1_funct_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_852, c_70])).
% 4.76/1.85  tff(c_864, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_6'), k1_relat_1('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_489, c_488, c_860])).
% 4.76/1.85  tff(c_52, plain, (![B_26, A_25, C_27]: (k1_xboole_0=B_26 | k1_relset_1(A_25, B_26, C_27)=A_25 | ~v1_funct_2(C_27, A_25, B_26) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.76/1.85  tff(c_916, plain, (k1_relat_1('#skF_6')=k1_xboole_0 | k1_relset_1(k2_relat_1('#skF_6'), k1_relat_1('#skF_6'), k2_funct_1('#skF_6'))=k2_relat_1('#skF_6') | ~v1_funct_2(k2_funct_1('#skF_6'), k2_relat_1('#skF_6'), k1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_864, c_52])).
% 4.76/1.85  tff(c_953, plain, (k1_relat_1('#skF_6')=k1_xboole_0 | k1_relset_1(k2_relat_1('#skF_6'), k1_relat_1('#skF_6'), k2_funct_1('#skF_6'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_854, c_916])).
% 4.76/1.85  tff(c_955, plain, $false, inference(negUnitSimplification, [status(thm)], [c_856, c_415, c_953])).
% 4.76/1.85  tff(c_957, plain, (k2_struct_0('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_223])).
% 4.76/1.85  tff(c_142, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_126, c_139])).
% 4.76/1.85  tff(c_147, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_142])).
% 4.76/1.85  tff(c_156, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_147])).
% 4.76/1.85  tff(c_985, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_957, c_156])).
% 4.76/1.85  tff(c_991, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_985])).
% 4.76/1.85  tff(c_992, plain, (k2_relset_1(k2_struct_0('#skF_5'), k2_struct_0('#skF_4'), k2_tops_2(k2_struct_0('#skF_4'), k2_struct_0('#skF_5'), '#skF_6'))!=k2_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_177])).
% 4.76/1.85  tff(c_1406, plain, (k2_relset_1(k2_struct_0('#skF_5'), k1_relat_1('#skF_6'), k2_tops_2(k1_relat_1('#skF_6'), k2_struct_0('#skF_5'), '#skF_6'))!=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1299, c_1299, c_1299, c_992])).
% 4.76/1.85  tff(c_1407, plain, (k2_relset_1(k2_relat_1('#skF_6'), k1_relat_1('#skF_6'), k2_tops_2(k1_relat_1('#skF_6'), k2_relat_1('#skF_6'), '#skF_6'))!=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1401, c_1401, c_1406])).
% 4.76/1.85  tff(c_1769, plain, (k2_relset_1(k2_relat_1('#skF_6'), k1_relat_1('#skF_6'), k2_funct_1('#skF_6'))!=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1765, c_1407])).
% 4.76/1.85  tff(c_1989, plain, (k2_relat_1(k2_funct_1('#skF_6'))!=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1854, c_1769])).
% 4.76/1.85  tff(c_1996, plain, (~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_26, c_1989])).
% 4.76/1.85  tff(c_2000, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_176, c_86, c_78, c_1996])).
% 4.76/1.85  tff(c_2002, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_147])).
% 4.76/1.85  tff(c_2259, plain, (v1_xboole_0(k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2254, c_2002])).
% 4.76/1.85  tff(c_24, plain, (![A_10]: (~v1_xboole_0(k1_relat_1(A_10)) | ~v1_relat_1(A_10) | v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.76/1.85  tff(c_2269, plain, (~v1_relat_1('#skF_6') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_2259, c_24])).
% 4.76/1.85  tff(c_2272, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2038, c_2269])).
% 4.76/1.85  tff(c_22, plain, (![A_9]: (v1_xboole_0(k2_relat_1(A_9)) | ~v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.76/1.85  tff(c_2258, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_2254, c_2017])).
% 4.76/1.85  tff(c_2356, plain, (![A_411, B_412, C_413]: (k2_relset_1(A_411, B_412, C_413)=k2_relat_1(C_413) | ~m1_subset_1(C_413, k1_zfmisc_1(k2_zfmisc_1(A_411, B_412))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.76/1.85  tff(c_2360, plain, (k2_relset_1(k1_relat_1('#skF_6'), k2_struct_0('#skF_5'), '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2258, c_2356])).
% 4.76/1.85  tff(c_2260, plain, (k2_relset_1(k1_relat_1('#skF_6'), k2_struct_0('#skF_5'), '#skF_6')=k2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2254, c_151])).
% 4.76/1.85  tff(c_2361, plain, (k2_struct_0('#skF_5')=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2360, c_2260])).
% 4.76/1.85  tff(c_2371, plain, (~v1_xboole_0(k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2361, c_150])).
% 4.76/1.85  tff(c_2379, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_22, c_2371])).
% 4.76/1.85  tff(c_2383, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2272, c_2379])).
% 4.76/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.76/1.85  
% 4.76/1.85  Inference rules
% 4.76/1.85  ----------------------
% 4.76/1.85  #Ref     : 0
% 4.76/1.85  #Sup     : 474
% 4.76/1.85  #Fact    : 0
% 4.76/1.85  #Define  : 0
% 4.76/1.85  #Split   : 14
% 4.76/1.85  #Chain   : 0
% 4.76/1.85  #Close   : 0
% 4.76/1.85  
% 4.76/1.85  Ordering : KBO
% 4.76/1.85  
% 4.76/1.85  Simplification rules
% 4.76/1.85  ----------------------
% 4.76/1.85  #Subsume      : 31
% 4.76/1.85  #Demod        : 366
% 4.76/1.85  #Tautology    : 207
% 4.76/1.85  #SimpNegUnit  : 21
% 4.76/1.85  #BackRed      : 88
% 4.76/1.85  
% 4.76/1.85  #Partial instantiations: 0
% 4.76/1.85  #Strategies tried      : 1
% 4.76/1.85  
% 4.76/1.85  Timing (in seconds)
% 4.76/1.85  ----------------------
% 4.76/1.85  Preprocessing        : 0.37
% 4.76/1.85  Parsing              : 0.19
% 4.76/1.85  CNF conversion       : 0.03
% 4.76/1.85  Main loop            : 0.68
% 4.76/1.85  Inferencing          : 0.27
% 4.76/1.85  Reduction            : 0.20
% 4.76/1.85  Demodulation         : 0.13
% 4.76/1.85  BG Simplification    : 0.03
% 4.76/1.85  Subsumption          : 0.11
% 4.76/1.85  Abstraction          : 0.03
% 4.76/1.85  MUC search           : 0.00
% 4.76/1.85  Cooper               : 0.00
% 4.76/1.85  Total                : 1.11
% 4.76/1.85  Index Insertion      : 0.00
% 4.76/1.85  Index Deletion       : 0.00
% 4.76/1.85  Index Matching       : 0.00
% 4.76/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
