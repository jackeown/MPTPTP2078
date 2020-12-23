%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:14 EST 2020

% Result     : Theorem 8.20s
% Output     : CNFRefutation 8.47s
% Verified   : 
% Statistics : Number of formulae       :  230 (10937 expanded)
%              Number of leaves         :   55 (3819 expanded)
%              Depth                    :   24
%              Number of atoms          :  392 (33119 expanded)
%              Number of equality atoms :  113 (10728 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k2_xboole_0 > k10_relat_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).

tff(f_141,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_149,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_121,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_113,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_161,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_173,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_tops_2(A,B,C))
        & v1_funct_2(k2_tops_2(A,B,C),B,A)
        & m1_subset_1(k2_tops_2(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_137,axiom,(
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

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_36,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).

tff(f_65,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(c_76,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_78,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_82,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_130,plain,(
    ! [A_64] :
      ( u1_struct_0(A_64) = k2_struct_0(A_64)
      | ~ l1_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_138,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_82,c_130])).

tff(c_137,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_130])).

tff(c_72,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_160,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_137,c_72])).

tff(c_4740,plain,(
    ! [A_423,B_424,C_425] :
      ( k2_relset_1(A_423,B_424,C_425) = k2_relat_1(C_425)
      | ~ m1_subset_1(C_425,k1_zfmisc_1(k2_zfmisc_1(A_423,B_424))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_4758,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_160,c_4740])).

tff(c_70,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_233,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_137,c_70])).

tff(c_4759,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4758,c_233])).

tff(c_56,plain,(
    ! [A_44] :
      ( ~ v1_xboole_0(k2_struct_0(A_44))
      | ~ l1_struct_0(A_44)
      | v2_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_4775,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4759,c_56])).

tff(c_4779,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_4775])).

tff(c_4780,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_4779])).

tff(c_302,plain,(
    ! [C_83,A_84,B_85] :
      ( v1_relat_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_315,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_160,c_302])).

tff(c_4617,plain,(
    ! [C_394,A_395,B_396] :
      ( v4_relat_1(C_394,A_395)
      | ~ m1_subset_1(C_394,k1_zfmisc_1(k2_zfmisc_1(A_395,B_396))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_4635,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_160,c_4617])).

tff(c_4717,plain,(
    ! [B_419,A_420] :
      ( k1_relat_1(B_419) = A_420
      | ~ v1_partfun1(B_419,A_420)
      | ~ v4_relat_1(B_419,A_420)
      | ~ v1_relat_1(B_419) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_4723,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4635,c_4717])).

tff(c_4727,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_315,c_4723])).

tff(c_4728,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_4727])).

tff(c_74,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_139,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_74])).

tff(c_161,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_139])).

tff(c_4769,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4759,c_161])).

tff(c_4770,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4759,c_160])).

tff(c_5147,plain,(
    ! [C_468,A_469,B_470] :
      ( v1_partfun1(C_468,A_469)
      | ~ v1_funct_2(C_468,A_469,B_470)
      | ~ v1_funct_1(C_468)
      | ~ m1_subset_1(C_468,k1_zfmisc_1(k2_zfmisc_1(A_469,B_470)))
      | v1_xboole_0(B_470) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_5150,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_4770,c_5147])).

tff(c_5166,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_4769,c_5150])).

tff(c_5168,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4780,c_4728,c_5166])).

tff(c_5169,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_4727])).

tff(c_5177,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5169,c_160])).

tff(c_5319,plain,(
    ! [A_482,B_483,C_484] :
      ( k2_relset_1(A_482,B_483,C_484) = k2_relat_1(C_484)
      | ~ m1_subset_1(C_484,k1_zfmisc_1(k2_zfmisc_1(A_482,B_483))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_5336,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_5177,c_5319])).

tff(c_5175,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5169,c_233])).

tff(c_5338,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5336,c_5175])).

tff(c_5176,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5169,c_161])).

tff(c_5346,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5338,c_5176])).

tff(c_5347,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5338,c_5177])).

tff(c_5343,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5338,c_5336])).

tff(c_68,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_7359,plain,(
    ! [A_586,B_587,C_588] :
      ( k2_tops_2(A_586,B_587,C_588) = k2_funct_1(C_588)
      | ~ v2_funct_1(C_588)
      | k2_relset_1(A_586,B_587,C_588) != B_587
      | ~ m1_subset_1(C_588,k1_zfmisc_1(k2_zfmisc_1(A_586,B_587)))
      | ~ v1_funct_2(C_588,A_586,B_587)
      | ~ v1_funct_1(C_588) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_7374,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_5347,c_7359])).

tff(c_7391,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_5346,c_5343,c_68,c_7374])).

tff(c_60,plain,(
    ! [A_48,B_49,C_50] :
      ( m1_subset_1(k2_tops_2(A_48,B_49,C_50),k1_zfmisc_1(k2_zfmisc_1(B_49,A_48)))
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49)))
      | ~ v1_funct_2(C_50,A_48,B_49)
      | ~ v1_funct_1(C_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_7494,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7391,c_60])).

tff(c_7498,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_5346,c_5347,c_7494])).

tff(c_38,plain,(
    ! [A_31,B_32,C_33] :
      ( k2_relset_1(A_31,B_32,C_33) = k2_relat_1(C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_7814,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_7498,c_38])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_148,plain,(
    ! [A_65,B_66] :
      ( v1_xboole_0(k2_zfmisc_1(A_65,B_66))
      | ~ v1_xboole_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_95,plain,(
    ! [B_60,A_61] :
      ( ~ v1_xboole_0(B_60)
      | B_60 = A_61
      | ~ v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_101,plain,(
    ! [A_61] :
      ( k1_xboole_0 = A_61
      | ~ v1_xboole_0(A_61) ) ),
    inference(resolution,[status(thm)],[c_2,c_95])).

tff(c_162,plain,(
    ! [A_67,B_68] :
      ( k2_zfmisc_1(A_67,B_68) = k1_xboole_0
      | ~ v1_xboole_0(A_67) ) ),
    inference(resolution,[status(thm)],[c_148,c_101])).

tff(c_171,plain,(
    ! [B_68] : k2_zfmisc_1(k1_xboole_0,B_68) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_162])).

tff(c_569,plain,(
    ! [A_138,B_139,C_140] :
      ( k2_relset_1(A_138,B_139,C_140) = k2_relat_1(C_140)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_587,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_160,c_569])).

tff(c_588,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_587,c_233])).

tff(c_603,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_588,c_56])).

tff(c_607,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_603])).

tff(c_608,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_607])).

tff(c_384,plain,(
    ! [C_101,A_102,B_103] :
      ( v4_relat_1(C_101,A_102)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_399,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_160,c_384])).

tff(c_546,plain,(
    ! [B_134,A_135] :
      ( k1_relat_1(B_134) = A_135
      | ~ v1_partfun1(B_134,A_135)
      | ~ v4_relat_1(B_134,A_135)
      | ~ v1_relat_1(B_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_552,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_399,c_546])).

tff(c_556,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_315,c_552])).

tff(c_557,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_556])).

tff(c_597,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_588,c_161])).

tff(c_598,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_588,c_160])).

tff(c_950,plain,(
    ! [C_174,A_175,B_176] :
      ( v1_partfun1(C_174,A_175)
      | ~ v1_funct_2(C_174,A_175,B_176)
      | ~ v1_funct_1(C_174)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(A_175,B_176)))
      | v1_xboole_0(B_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_953,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_598,c_950])).

tff(c_969,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_597,c_953])).

tff(c_971,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_608,c_557,c_969])).

tff(c_972,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_556])).

tff(c_979,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_972,c_160])).

tff(c_1063,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_979,c_38])).

tff(c_977,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_972,c_233])).

tff(c_1079,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1063,c_977])).

tff(c_978,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_972,c_161])).

tff(c_1087,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1079,c_978])).

tff(c_1085,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1079,c_979])).

tff(c_1084,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1079,c_1063])).

tff(c_3157,plain,(
    ! [A_291,B_292,C_293] :
      ( k2_tops_2(A_291,B_292,C_293) = k2_funct_1(C_293)
      | ~ v2_funct_1(C_293)
      | k2_relset_1(A_291,B_292,C_293) != B_292
      | ~ m1_subset_1(C_293,k1_zfmisc_1(k2_zfmisc_1(A_291,B_292)))
      | ~ v1_funct_2(C_293,A_291,B_292)
      | ~ v1_funct_1(C_293) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_3172,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1085,c_3157])).

tff(c_3189,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1087,c_1084,c_68,c_3172])).

tff(c_3199,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3189,c_60])).

tff(c_3203,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1087,c_1085,c_3199])).

tff(c_36,plain,(
    ! [A_28,B_29,C_30] :
      ( k1_relset_1(A_28,B_29,C_30) = k1_relat_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_3268,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3203,c_36])).

tff(c_66,plain,
    ( k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_327,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_138,c_137,c_137,c_138,c_138,c_137,c_137,c_66])).

tff(c_328,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_327])).

tff(c_974,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_972,c_972,c_328])).

tff(c_1215,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1079,c_1079,c_1079,c_974])).

tff(c_3193,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3189,c_1215])).

tff(c_3391,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3268,c_3193])).

tff(c_984,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_3'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_972,c_56])).

tff(c_988,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_3'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_984])).

tff(c_1008,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_988])).

tff(c_2483,plain,(
    ! [C_260,A_261,B_262] :
      ( v1_funct_1(k2_funct_1(C_260))
      | k2_relset_1(A_261,B_262,C_260) != B_262
      | ~ v2_funct_1(C_260)
      | ~ m1_subset_1(C_260,k1_zfmisc_1(k2_zfmisc_1(A_261,B_262)))
      | ~ v1_funct_2(C_260,A_261,B_262)
      | ~ v1_funct_1(C_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_2495,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1085,c_2483])).

tff(c_2512,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1087,c_68,c_1084,c_2495])).

tff(c_2541,plain,(
    ! [C_267,B_268,A_269] :
      ( v1_funct_2(k2_funct_1(C_267),B_268,A_269)
      | k2_relset_1(A_269,B_268,C_267) != B_268
      | ~ v2_funct_1(C_267)
      | ~ m1_subset_1(C_267,k1_zfmisc_1(k2_zfmisc_1(A_269,B_268)))
      | ~ v1_funct_2(C_267,A_269,B_268)
      | ~ v1_funct_1(C_267) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_2553,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1085,c_2541])).

tff(c_2570,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1087,c_68,c_1084,c_2553])).

tff(c_40,plain,(
    ! [C_37,A_34,B_35] :
      ( v1_partfun1(C_37,A_34)
      | ~ v1_funct_2(C_37,A_34,B_35)
      | ~ v1_funct_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35)))
      | v1_xboole_0(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_3218,plain,
    ( v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | v1_xboole_0(k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3203,c_40])).

tff(c_3263,plain,
    ( v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | v1_xboole_0(k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2512,c_2570,c_3218])).

tff(c_3264,plain,(
    v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_1008,c_3263])).

tff(c_30,plain,(
    ! [C_24,A_22,B_23] :
      ( v1_relat_1(C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_3275,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3203,c_30])).

tff(c_34,plain,(
    ! [C_27,A_25,B_26] :
      ( v4_relat_1(C_27,A_25)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_3271,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3203,c_34])).

tff(c_46,plain,(
    ! [B_39,A_38] :
      ( k1_relat_1(B_39) = A_38
      | ~ v1_partfun1(B_39,A_38)
      | ~ v4_relat_1(B_39,A_38)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_3280,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3271,c_46])).

tff(c_3283,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3275,c_3280])).

tff(c_3401,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3264,c_3283])).

tff(c_3402,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3391,c_3401])).

tff(c_3404,plain,(
    v1_xboole_0(k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_988])).

tff(c_3429,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3404,c_101])).

tff(c_212,plain,(
    ! [A_71,B_72] :
      ( r1_tarski(A_71,B_72)
      | ~ m1_subset_1(A_71,k1_zfmisc_1(B_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_216,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_160,c_212])).

tff(c_976,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_972,c_216])).

tff(c_3516,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_3429,c_976])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_3534,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3516,c_8])).

tff(c_3590,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3534,c_2])).

tff(c_20,plain,(
    ! [A_15] :
      ( v1_xboole_0(k2_relat_1(A_15))
      | ~ v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_102,plain,(
    ! [A_62] :
      ( k1_xboole_0 = A_62
      | ~ v1_xboole_0(A_62) ) ),
    inference(resolution,[status(thm)],[c_2,c_95])).

tff(c_112,plain,(
    ! [A_63] :
      ( k2_relat_1(A_63) = k1_xboole_0
      | ~ v1_xboole_0(A_63) ) ),
    inference(resolution,[status(thm)],[c_20,c_102])).

tff(c_120,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_112])).

tff(c_3585,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3534,c_3534,c_120])).

tff(c_3535,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_3429,c_979])).

tff(c_3560,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3534,c_3535])).

tff(c_3498,plain,(
    ! [A_300,B_301,C_302] :
      ( k2_relset_1(A_300,B_301,C_302) = k2_relat_1(C_302)
      | ~ m1_subset_1(C_302,k1_zfmisc_1(k2_zfmisc_1(A_300,B_301))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_3511,plain,(
    ! [B_68,C_302] :
      ( k2_relset_1(k1_xboole_0,B_68,C_302) = k2_relat_1(C_302)
      | ~ m1_subset_1(C_302,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_3498])).

tff(c_4464,plain,(
    ! [B_374,C_375] :
      ( k2_relset_1('#skF_3',B_374,C_375) = k2_relat_1(C_375)
      | ~ m1_subset_1(C_375,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3534,c_3534,c_3511])).

tff(c_4466,plain,(
    ! [B_374] : k2_relset_1('#skF_3',B_374,'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3560,c_4464])).

tff(c_4471,plain,(
    ! [B_374] : k2_relset_1('#skF_3',B_374,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3585,c_4466])).

tff(c_3485,plain,(
    k2_relset_1(k1_xboole_0,k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3429,c_977])).

tff(c_3564,plain,(
    k2_relset_1('#skF_3',k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3534,c_3485])).

tff(c_4473,plain,(
    k2_struct_0('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4471,c_3564])).

tff(c_4487,plain,
    ( ~ v1_xboole_0('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4473,c_56])).

tff(c_4491,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_3590,c_4487])).

tff(c_4493,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_4491])).

tff(c_4494,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_327])).

tff(c_5173,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5169,c_5169,c_5169,c_4494])).

tff(c_5449,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5338,c_5338,c_5173])).

tff(c_7488,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7391,c_5449])).

tff(c_7943,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7814,c_7488])).

tff(c_22,plain,(
    ! [A_16,B_17] : v1_relat_1(k2_zfmisc_1(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_18,plain,(
    ! [B_14,A_12] :
      ( v1_relat_1(B_14)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_12))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_7782,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_7498,c_18])).

tff(c_7821,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_7782])).

tff(c_4495,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) = k2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_327])).

tff(c_5171,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')) = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5169,c_5169,c_4495])).

tff(c_5633,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5338,c_5338,c_5338,c_5171])).

tff(c_7486,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7391,c_5633])).

tff(c_7773,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_7498,c_36])).

tff(c_7816,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7486,c_7773])).

tff(c_24,plain,(
    ! [A_18] :
      ( k9_relat_1(A_18,k1_relat_1(A_18)) = k2_relat_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_7837,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7816,c_24])).

tff(c_7843,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7821,c_7837])).

tff(c_28,plain,(
    ! [B_21,A_20] :
      ( k9_relat_1(k2_funct_1(B_21),A_20) = k10_relat_1(B_21,A_20)
      | ~ v2_funct_1(B_21)
      | ~ v1_funct_1(B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_7918,plain,
    ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7843,c_28])).

tff(c_7925,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_315,c_76,c_68,c_7918])).

tff(c_26,plain,(
    ! [A_19] :
      ( k10_relat_1(A_19,k2_relat_1(A_19)) = k1_relat_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_7932,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7925,c_26])).

tff(c_7939,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_315,c_7932])).

tff(c_7948,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7943,c_7939])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:17:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.20/2.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.25/2.69  
% 8.25/2.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.25/2.70  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k2_xboole_0 > k10_relat_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 8.25/2.70  
% 8.25/2.70  %Foreground sorts:
% 8.25/2.70  
% 8.25/2.70  
% 8.25/2.70  %Background operators:
% 8.25/2.70  
% 8.25/2.70  
% 8.25/2.70  %Foreground operators:
% 8.25/2.70  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.25/2.70  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.25/2.70  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.25/2.70  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 8.25/2.70  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.25/2.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.25/2.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.25/2.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.25/2.70  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.25/2.70  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 8.25/2.70  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.25/2.70  tff('#skF_2', type, '#skF_2': $i).
% 8.25/2.70  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 8.25/2.70  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 8.25/2.70  tff('#skF_3', type, '#skF_3': $i).
% 8.25/2.70  tff('#skF_1', type, '#skF_1': $i).
% 8.25/2.70  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.25/2.70  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.25/2.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.25/2.70  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 8.25/2.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.25/2.70  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 8.25/2.70  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.25/2.70  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.25/2.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.25/2.70  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.25/2.70  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.25/2.70  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.25/2.70  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 8.25/2.70  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.25/2.70  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.25/2.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.25/2.70  
% 8.47/2.73  tff(f_197, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_2)).
% 8.47/2.73  tff(f_141, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 8.47/2.73  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.47/2.73  tff(f_149, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_struct_0)).
% 8.47/2.73  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.47/2.73  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.47/2.73  tff(f_121, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 8.47/2.73  tff(f_113, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 8.47/2.73  tff(f_161, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 8.47/2.73  tff(f_173, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v1_funct_1(k2_tops_2(A, B, C)) & v1_funct_2(k2_tops_2(A, B, C), B, A)) & m1_subset_1(k2_tops_2(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_2)).
% 8.47/2.73  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 8.47/2.73  tff(f_48, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 8.47/2.73  tff(f_44, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 8.47/2.73  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.47/2.73  tff(f_137, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 8.47/2.73  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 8.47/2.73  tff(f_36, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 8.47/2.73  tff(f_63, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc11_relat_1)).
% 8.47/2.73  tff(f_65, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.47/2.73  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 8.47/2.73  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 8.47/2.73  tff(f_81, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_1)).
% 8.47/2.73  tff(f_73, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 8.47/2.73  tff(c_76, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_197])).
% 8.47/2.73  tff(c_80, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_197])).
% 8.47/2.73  tff(c_78, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_197])).
% 8.47/2.73  tff(c_82, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_197])).
% 8.47/2.73  tff(c_130, plain, (![A_64]: (u1_struct_0(A_64)=k2_struct_0(A_64) | ~l1_struct_0(A_64))), inference(cnfTransformation, [status(thm)], [f_141])).
% 8.47/2.73  tff(c_138, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_82, c_130])).
% 8.47/2.73  tff(c_137, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_78, c_130])).
% 8.47/2.73  tff(c_72, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_197])).
% 8.47/2.73  tff(c_160, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_137, c_72])).
% 8.47/2.73  tff(c_4740, plain, (![A_423, B_424, C_425]: (k2_relset_1(A_423, B_424, C_425)=k2_relat_1(C_425) | ~m1_subset_1(C_425, k1_zfmisc_1(k2_zfmisc_1(A_423, B_424))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.47/2.73  tff(c_4758, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_160, c_4740])).
% 8.47/2.73  tff(c_70, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_197])).
% 8.47/2.73  tff(c_233, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_138, c_137, c_70])).
% 8.47/2.73  tff(c_4759, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4758, c_233])).
% 8.47/2.73  tff(c_56, plain, (![A_44]: (~v1_xboole_0(k2_struct_0(A_44)) | ~l1_struct_0(A_44) | v2_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_149])).
% 8.47/2.73  tff(c_4775, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4759, c_56])).
% 8.47/2.73  tff(c_4779, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_4775])).
% 8.47/2.73  tff(c_4780, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_80, c_4779])).
% 8.47/2.73  tff(c_302, plain, (![C_83, A_84, B_85]: (v1_relat_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.47/2.73  tff(c_315, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_160, c_302])).
% 8.47/2.73  tff(c_4617, plain, (![C_394, A_395, B_396]: (v4_relat_1(C_394, A_395) | ~m1_subset_1(C_394, k1_zfmisc_1(k2_zfmisc_1(A_395, B_396))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.47/2.73  tff(c_4635, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_160, c_4617])).
% 8.47/2.73  tff(c_4717, plain, (![B_419, A_420]: (k1_relat_1(B_419)=A_420 | ~v1_partfun1(B_419, A_420) | ~v4_relat_1(B_419, A_420) | ~v1_relat_1(B_419))), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.47/2.73  tff(c_4723, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4635, c_4717])).
% 8.47/2.73  tff(c_4727, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_315, c_4723])).
% 8.47/2.73  tff(c_4728, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_4727])).
% 8.47/2.73  tff(c_74, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_197])).
% 8.47/2.73  tff(c_139, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_74])).
% 8.47/2.73  tff(c_161, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_139])).
% 8.47/2.73  tff(c_4769, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4759, c_161])).
% 8.47/2.73  tff(c_4770, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_4759, c_160])).
% 8.47/2.73  tff(c_5147, plain, (![C_468, A_469, B_470]: (v1_partfun1(C_468, A_469) | ~v1_funct_2(C_468, A_469, B_470) | ~v1_funct_1(C_468) | ~m1_subset_1(C_468, k1_zfmisc_1(k2_zfmisc_1(A_469, B_470))) | v1_xboole_0(B_470))), inference(cnfTransformation, [status(thm)], [f_113])).
% 8.47/2.73  tff(c_5150, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_4770, c_5147])).
% 8.47/2.73  tff(c_5166, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_4769, c_5150])).
% 8.47/2.73  tff(c_5168, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4780, c_4728, c_5166])).
% 8.47/2.73  tff(c_5169, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_4727])).
% 8.47/2.73  tff(c_5177, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_5169, c_160])).
% 8.47/2.73  tff(c_5319, plain, (![A_482, B_483, C_484]: (k2_relset_1(A_482, B_483, C_484)=k2_relat_1(C_484) | ~m1_subset_1(C_484, k1_zfmisc_1(k2_zfmisc_1(A_482, B_483))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.47/2.73  tff(c_5336, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_5177, c_5319])).
% 8.47/2.73  tff(c_5175, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5169, c_233])).
% 8.47/2.73  tff(c_5338, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5336, c_5175])).
% 8.47/2.73  tff(c_5176, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_5169, c_161])).
% 8.47/2.73  tff(c_5346, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5338, c_5176])).
% 8.47/2.73  tff(c_5347, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_5338, c_5177])).
% 8.47/2.73  tff(c_5343, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5338, c_5336])).
% 8.47/2.73  tff(c_68, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_197])).
% 8.47/2.73  tff(c_7359, plain, (![A_586, B_587, C_588]: (k2_tops_2(A_586, B_587, C_588)=k2_funct_1(C_588) | ~v2_funct_1(C_588) | k2_relset_1(A_586, B_587, C_588)!=B_587 | ~m1_subset_1(C_588, k1_zfmisc_1(k2_zfmisc_1(A_586, B_587))) | ~v1_funct_2(C_588, A_586, B_587) | ~v1_funct_1(C_588))), inference(cnfTransformation, [status(thm)], [f_161])).
% 8.47/2.73  tff(c_7374, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_5347, c_7359])).
% 8.47/2.73  tff(c_7391, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_5346, c_5343, c_68, c_7374])).
% 8.47/2.73  tff(c_60, plain, (![A_48, B_49, C_50]: (m1_subset_1(k2_tops_2(A_48, B_49, C_50), k1_zfmisc_1(k2_zfmisc_1(B_49, A_48))) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))) | ~v1_funct_2(C_50, A_48, B_49) | ~v1_funct_1(C_50))), inference(cnfTransformation, [status(thm)], [f_173])).
% 8.47/2.73  tff(c_7494, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7391, c_60])).
% 8.47/2.73  tff(c_7498, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_5346, c_5347, c_7494])).
% 8.47/2.73  tff(c_38, plain, (![A_31, B_32, C_33]: (k2_relset_1(A_31, B_32, C_33)=k2_relat_1(C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.47/2.73  tff(c_7814, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_7498, c_38])).
% 8.47/2.73  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 8.47/2.73  tff(c_148, plain, (![A_65, B_66]: (v1_xboole_0(k2_zfmisc_1(A_65, B_66)) | ~v1_xboole_0(A_65))), inference(cnfTransformation, [status(thm)], [f_48])).
% 8.47/2.73  tff(c_95, plain, (![B_60, A_61]: (~v1_xboole_0(B_60) | B_60=A_61 | ~v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.47/2.73  tff(c_101, plain, (![A_61]: (k1_xboole_0=A_61 | ~v1_xboole_0(A_61))), inference(resolution, [status(thm)], [c_2, c_95])).
% 8.47/2.73  tff(c_162, plain, (![A_67, B_68]: (k2_zfmisc_1(A_67, B_68)=k1_xboole_0 | ~v1_xboole_0(A_67))), inference(resolution, [status(thm)], [c_148, c_101])).
% 8.47/2.73  tff(c_171, plain, (![B_68]: (k2_zfmisc_1(k1_xboole_0, B_68)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_162])).
% 8.47/2.73  tff(c_569, plain, (![A_138, B_139, C_140]: (k2_relset_1(A_138, B_139, C_140)=k2_relat_1(C_140) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.47/2.73  tff(c_587, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_160, c_569])).
% 8.47/2.73  tff(c_588, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_587, c_233])).
% 8.47/2.73  tff(c_603, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_588, c_56])).
% 8.47/2.73  tff(c_607, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_603])).
% 8.47/2.73  tff(c_608, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_80, c_607])).
% 8.47/2.73  tff(c_384, plain, (![C_101, A_102, B_103]: (v4_relat_1(C_101, A_102) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.47/2.73  tff(c_399, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_160, c_384])).
% 8.47/2.73  tff(c_546, plain, (![B_134, A_135]: (k1_relat_1(B_134)=A_135 | ~v1_partfun1(B_134, A_135) | ~v4_relat_1(B_134, A_135) | ~v1_relat_1(B_134))), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.47/2.73  tff(c_552, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_399, c_546])).
% 8.47/2.73  tff(c_556, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_315, c_552])).
% 8.47/2.73  tff(c_557, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_556])).
% 8.47/2.73  tff(c_597, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_588, c_161])).
% 8.47/2.73  tff(c_598, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_588, c_160])).
% 8.47/2.73  tff(c_950, plain, (![C_174, A_175, B_176]: (v1_partfun1(C_174, A_175) | ~v1_funct_2(C_174, A_175, B_176) | ~v1_funct_1(C_174) | ~m1_subset_1(C_174, k1_zfmisc_1(k2_zfmisc_1(A_175, B_176))) | v1_xboole_0(B_176))), inference(cnfTransformation, [status(thm)], [f_113])).
% 8.47/2.73  tff(c_953, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_598, c_950])).
% 8.47/2.73  tff(c_969, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_597, c_953])).
% 8.47/2.73  tff(c_971, plain, $false, inference(negUnitSimplification, [status(thm)], [c_608, c_557, c_969])).
% 8.47/2.73  tff(c_972, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_556])).
% 8.47/2.73  tff(c_979, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_972, c_160])).
% 8.47/2.73  tff(c_1063, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_979, c_38])).
% 8.47/2.73  tff(c_977, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_972, c_233])).
% 8.47/2.73  tff(c_1079, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1063, c_977])).
% 8.47/2.73  tff(c_978, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_972, c_161])).
% 8.47/2.73  tff(c_1087, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1079, c_978])).
% 8.47/2.73  tff(c_1085, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_1079, c_979])).
% 8.47/2.73  tff(c_1084, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1079, c_1063])).
% 8.47/2.73  tff(c_3157, plain, (![A_291, B_292, C_293]: (k2_tops_2(A_291, B_292, C_293)=k2_funct_1(C_293) | ~v2_funct_1(C_293) | k2_relset_1(A_291, B_292, C_293)!=B_292 | ~m1_subset_1(C_293, k1_zfmisc_1(k2_zfmisc_1(A_291, B_292))) | ~v1_funct_2(C_293, A_291, B_292) | ~v1_funct_1(C_293))), inference(cnfTransformation, [status(thm)], [f_161])).
% 8.47/2.73  tff(c_3172, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1085, c_3157])).
% 8.47/2.73  tff(c_3189, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1087, c_1084, c_68, c_3172])).
% 8.47/2.73  tff(c_3199, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3189, c_60])).
% 8.47/2.73  tff(c_3203, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1087, c_1085, c_3199])).
% 8.47/2.73  tff(c_36, plain, (![A_28, B_29, C_30]: (k1_relset_1(A_28, B_29, C_30)=k1_relat_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.47/2.73  tff(c_3268, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_3203, c_36])).
% 8.47/2.73  tff(c_66, plain, (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_197])).
% 8.47/2.73  tff(c_327, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_138, c_138, c_137, c_137, c_138, c_138, c_137, c_137, c_66])).
% 8.47/2.73  tff(c_328, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_327])).
% 8.47/2.73  tff(c_974, plain, (k1_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_972, c_972, c_328])).
% 8.47/2.73  tff(c_1215, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1079, c_1079, c_1079, c_974])).
% 8.47/2.73  tff(c_3193, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3189, c_1215])).
% 8.47/2.73  tff(c_3391, plain, (k1_relat_1(k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3268, c_3193])).
% 8.47/2.73  tff(c_984, plain, (~v1_xboole_0(k1_relat_1('#skF_3')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_972, c_56])).
% 8.47/2.73  tff(c_988, plain, (~v1_xboole_0(k1_relat_1('#skF_3')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_984])).
% 8.47/2.73  tff(c_1008, plain, (~v1_xboole_0(k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_988])).
% 8.47/2.73  tff(c_2483, plain, (![C_260, A_261, B_262]: (v1_funct_1(k2_funct_1(C_260)) | k2_relset_1(A_261, B_262, C_260)!=B_262 | ~v2_funct_1(C_260) | ~m1_subset_1(C_260, k1_zfmisc_1(k2_zfmisc_1(A_261, B_262))) | ~v1_funct_2(C_260, A_261, B_262) | ~v1_funct_1(C_260))), inference(cnfTransformation, [status(thm)], [f_137])).
% 8.47/2.73  tff(c_2495, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1085, c_2483])).
% 8.47/2.73  tff(c_2512, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1087, c_68, c_1084, c_2495])).
% 8.47/2.73  tff(c_2541, plain, (![C_267, B_268, A_269]: (v1_funct_2(k2_funct_1(C_267), B_268, A_269) | k2_relset_1(A_269, B_268, C_267)!=B_268 | ~v2_funct_1(C_267) | ~m1_subset_1(C_267, k1_zfmisc_1(k2_zfmisc_1(A_269, B_268))) | ~v1_funct_2(C_267, A_269, B_268) | ~v1_funct_1(C_267))), inference(cnfTransformation, [status(thm)], [f_137])).
% 8.47/2.73  tff(c_2553, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1085, c_2541])).
% 8.47/2.73  tff(c_2570, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1087, c_68, c_1084, c_2553])).
% 8.47/2.73  tff(c_40, plain, (![C_37, A_34, B_35]: (v1_partfun1(C_37, A_34) | ~v1_funct_2(C_37, A_34, B_35) | ~v1_funct_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))) | v1_xboole_0(B_35))), inference(cnfTransformation, [status(thm)], [f_113])).
% 8.47/2.73  tff(c_3218, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | v1_xboole_0(k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_3203, c_40])).
% 8.47/2.73  tff(c_3263, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | v1_xboole_0(k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2512, c_2570, c_3218])).
% 8.47/2.73  tff(c_3264, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_1008, c_3263])).
% 8.47/2.73  tff(c_30, plain, (![C_24, A_22, B_23]: (v1_relat_1(C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.47/2.73  tff(c_3275, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_3203, c_30])).
% 8.47/2.73  tff(c_34, plain, (![C_27, A_25, B_26]: (v4_relat_1(C_27, A_25) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.47/2.73  tff(c_3271, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_3203, c_34])).
% 8.47/2.73  tff(c_46, plain, (![B_39, A_38]: (k1_relat_1(B_39)=A_38 | ~v1_partfun1(B_39, A_38) | ~v4_relat_1(B_39, A_38) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.47/2.73  tff(c_3280, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_3271, c_46])).
% 8.47/2.73  tff(c_3283, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3275, c_3280])).
% 8.47/2.73  tff(c_3401, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3264, c_3283])).
% 8.47/2.73  tff(c_3402, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3391, c_3401])).
% 8.47/2.73  tff(c_3404, plain, (v1_xboole_0(k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_988])).
% 8.47/2.73  tff(c_3429, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_3404, c_101])).
% 8.47/2.73  tff(c_212, plain, (![A_71, B_72]: (r1_tarski(A_71, B_72) | ~m1_subset_1(A_71, k1_zfmisc_1(B_72)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.47/2.73  tff(c_216, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_160, c_212])).
% 8.47/2.73  tff(c_976, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_972, c_216])).
% 8.47/2.73  tff(c_3516, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_171, c_3429, c_976])).
% 8.47/2.73  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.47/2.73  tff(c_3534, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_3516, c_8])).
% 8.47/2.73  tff(c_3590, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3534, c_2])).
% 8.47/2.73  tff(c_20, plain, (![A_15]: (v1_xboole_0(k2_relat_1(A_15)) | ~v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.47/2.73  tff(c_102, plain, (![A_62]: (k1_xboole_0=A_62 | ~v1_xboole_0(A_62))), inference(resolution, [status(thm)], [c_2, c_95])).
% 8.47/2.73  tff(c_112, plain, (![A_63]: (k2_relat_1(A_63)=k1_xboole_0 | ~v1_xboole_0(A_63))), inference(resolution, [status(thm)], [c_20, c_102])).
% 8.47/2.73  tff(c_120, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_112])).
% 8.47/2.73  tff(c_3585, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3534, c_3534, c_120])).
% 8.47/2.73  tff(c_3535, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_171, c_3429, c_979])).
% 8.47/2.73  tff(c_3560, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3534, c_3535])).
% 8.47/2.73  tff(c_3498, plain, (![A_300, B_301, C_302]: (k2_relset_1(A_300, B_301, C_302)=k2_relat_1(C_302) | ~m1_subset_1(C_302, k1_zfmisc_1(k2_zfmisc_1(A_300, B_301))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.47/2.73  tff(c_3511, plain, (![B_68, C_302]: (k2_relset_1(k1_xboole_0, B_68, C_302)=k2_relat_1(C_302) | ~m1_subset_1(C_302, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_171, c_3498])).
% 8.47/2.73  tff(c_4464, plain, (![B_374, C_375]: (k2_relset_1('#skF_3', B_374, C_375)=k2_relat_1(C_375) | ~m1_subset_1(C_375, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_3534, c_3534, c_3511])).
% 8.47/2.73  tff(c_4466, plain, (![B_374]: (k2_relset_1('#skF_3', B_374, '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_3560, c_4464])).
% 8.47/2.73  tff(c_4471, plain, (![B_374]: (k2_relset_1('#skF_3', B_374, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3585, c_4466])).
% 8.47/2.73  tff(c_3485, plain, (k2_relset_1(k1_xboole_0, k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3429, c_977])).
% 8.47/2.73  tff(c_3564, plain, (k2_relset_1('#skF_3', k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3534, c_3485])).
% 8.47/2.73  tff(c_4473, plain, (k2_struct_0('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4471, c_3564])).
% 8.47/2.73  tff(c_4487, plain, (~v1_xboole_0('#skF_3') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4473, c_56])).
% 8.47/2.73  tff(c_4491, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_3590, c_4487])).
% 8.47/2.73  tff(c_4493, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_4491])).
% 8.47/2.73  tff(c_4494, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_327])).
% 8.47/2.73  tff(c_5173, plain, (k2_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5169, c_5169, c_5169, c_4494])).
% 8.47/2.73  tff(c_5449, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5338, c_5338, c_5173])).
% 8.47/2.73  tff(c_7488, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7391, c_5449])).
% 8.47/2.73  tff(c_7943, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7814, c_7488])).
% 8.47/2.73  tff(c_22, plain, (![A_16, B_17]: (v1_relat_1(k2_zfmisc_1(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.47/2.73  tff(c_18, plain, (![B_14, A_12]: (v1_relat_1(B_14) | ~m1_subset_1(B_14, k1_zfmisc_1(A_12)) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.47/2.73  tff(c_7782, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3')))), inference(resolution, [status(thm)], [c_7498, c_18])).
% 8.47/2.73  tff(c_7821, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_7782])).
% 8.47/2.73  tff(c_4495, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))=k2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_327])).
% 8.47/2.73  tff(c_5171, plain, (k1_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3'))=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5169, c_5169, c_4495])).
% 8.47/2.73  tff(c_5633, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5338, c_5338, c_5338, c_5171])).
% 8.47/2.73  tff(c_7486, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7391, c_5633])).
% 8.47/2.73  tff(c_7773, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_7498, c_36])).
% 8.47/2.73  tff(c_7816, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7486, c_7773])).
% 8.47/2.73  tff(c_24, plain, (![A_18]: (k9_relat_1(A_18, k1_relat_1(A_18))=k2_relat_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.47/2.73  tff(c_7837, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_7816, c_24])).
% 8.47/2.73  tff(c_7843, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_7821, c_7837])).
% 8.47/2.73  tff(c_28, plain, (![B_21, A_20]: (k9_relat_1(k2_funct_1(B_21), A_20)=k10_relat_1(B_21, A_20) | ~v2_funct_1(B_21) | ~v1_funct_1(B_21) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.47/2.73  tff(c_7918, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7843, c_28])).
% 8.47/2.73  tff(c_7925, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_315, c_76, c_68, c_7918])).
% 8.47/2.73  tff(c_26, plain, (![A_19]: (k10_relat_1(A_19, k2_relat_1(A_19))=k1_relat_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.47/2.73  tff(c_7932, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7925, c_26])).
% 8.47/2.73  tff(c_7939, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_315, c_7932])).
% 8.47/2.73  tff(c_7948, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7943, c_7939])).
% 8.47/2.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.47/2.73  
% 8.47/2.73  Inference rules
% 8.47/2.73  ----------------------
% 8.47/2.73  #Ref     : 0
% 8.47/2.73  #Sup     : 2106
% 8.47/2.73  #Fact    : 0
% 8.47/2.73  #Define  : 0
% 8.47/2.73  #Split   : 14
% 8.47/2.73  #Chain   : 0
% 8.47/2.73  #Close   : 0
% 8.47/2.73  
% 8.47/2.73  Ordering : KBO
% 8.47/2.73  
% 8.47/2.73  Simplification rules
% 8.47/2.73  ----------------------
% 8.47/2.73  #Subsume      : 677
% 8.47/2.73  #Demod        : 1006
% 8.47/2.73  #Tautology    : 557
% 8.47/2.73  #SimpNegUnit  : 33
% 8.47/2.73  #BackRed      : 105
% 8.47/2.73  
% 8.47/2.73  #Partial instantiations: 0
% 8.47/2.73  #Strategies tried      : 1
% 8.47/2.73  
% 8.47/2.73  Timing (in seconds)
% 8.47/2.73  ----------------------
% 8.47/2.73  Preprocessing        : 0.38
% 8.47/2.73  Parsing              : 0.20
% 8.47/2.73  CNF conversion       : 0.03
% 8.47/2.73  Main loop            : 1.55
% 8.47/2.73  Inferencing          : 0.49
% 8.47/2.73  Reduction            : 0.47
% 8.47/2.73  Demodulation         : 0.32
% 8.47/2.73  BG Simplification    : 0.07
% 8.47/2.73  Subsumption          : 0.40
% 8.47/2.73  Abstraction          : 0.07
% 8.47/2.73  MUC search           : 0.00
% 8.47/2.73  Cooper               : 0.00
% 8.47/2.73  Total                : 2.00
% 8.47/2.73  Index Insertion      : 0.00
% 8.47/2.73  Index Deletion       : 0.00
% 8.47/2.73  Index Matching       : 0.00
% 8.47/2.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
