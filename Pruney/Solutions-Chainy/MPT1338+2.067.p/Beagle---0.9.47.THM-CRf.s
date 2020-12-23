%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:24 EST 2020

% Result     : Theorem 8.45s
% Output     : CNFRefutation 8.79s
% Verified   : 
% Statistics : Number of formulae       :  292 (87430 expanded)
%              Number of leaves         :   57 (30331 expanded)
%              Depth                    :   39
%              Number of atoms          :  700 (263089 expanded)
%              Number of equality atoms :  155 (81315 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k6_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(f_221,negated_conjecture,(
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

tff(f_177,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_131,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_185,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

tff(f_44,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_119,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_157,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_149,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_197,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_60,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_135,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_123,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k8_relset_1(A,B,C,D),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_173,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_72,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_113,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_52,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_105,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_95,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A)
              & v2_funct_1(A) )
           => r1_tarski(k1_relat_1(A),k2_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_funct_1)).

tff(f_127,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_84,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_88,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_86,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_90,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_112,plain,(
    ! [A_61] :
      ( u1_struct_0(A_61) = k2_struct_0(A_61)
      | ~ l1_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_120,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_90,c_112])).

tff(c_119,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_86,c_112])).

tff(c_80,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_140,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_119,c_80])).

tff(c_5214,plain,(
    ! [A_653,B_654,C_655] :
      ( k2_relset_1(A_653,B_654,C_655) = k2_relat_1(C_655)
      | ~ m1_subset_1(C_655,k1_zfmisc_1(k2_zfmisc_1(A_653,B_654))) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_5222,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_140,c_5214])).

tff(c_78,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_155,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_119,c_78])).

tff(c_5224,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5222,c_155])).

tff(c_70,plain,(
    ! [A_48] :
      ( ~ v1_xboole_0(k2_struct_0(A_48))
      | ~ l1_struct_0(A_48)
      | v2_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_5241,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5224,c_70])).

tff(c_5245,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_5241])).

tff(c_5246,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_5245])).

tff(c_14,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_173,plain,(
    ! [B_72,A_73] :
      ( v1_relat_1(B_72)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_73))
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_176,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_140,c_173])).

tff(c_182,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_176])).

tff(c_5130,plain,(
    ! [C_634,A_635,B_636] :
      ( v4_relat_1(C_634,A_635)
      | ~ m1_subset_1(C_634,k1_zfmisc_1(k2_zfmisc_1(A_635,B_636))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_5138,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_140,c_5130])).

tff(c_5184,plain,(
    ! [B_645,A_646] :
      ( k1_relat_1(B_645) = A_646
      | ~ v1_partfun1(B_645,A_646)
      | ~ v4_relat_1(B_645,A_646)
      | ~ v1_relat_1(B_645) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_5190,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_5138,c_5184])).

tff(c_5196,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_5190])).

tff(c_5197,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_5196])).

tff(c_82,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_121,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_82])).

tff(c_130,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_121])).

tff(c_5236,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5224,c_130])).

tff(c_5235,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5224,c_140])).

tff(c_5593,plain,(
    ! [C_701,A_702,B_703] :
      ( v1_partfun1(C_701,A_702)
      | ~ v1_funct_2(C_701,A_702,B_703)
      | ~ v1_funct_1(C_701)
      | ~ m1_subset_1(C_701,k1_zfmisc_1(k2_zfmisc_1(A_702,B_703)))
      | v1_xboole_0(B_703) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_5600,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_5235,c_5593])).

tff(c_5608,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_5236,c_5600])).

tff(c_5610,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5246,c_5197,c_5608])).

tff(c_5611,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_5196])).

tff(c_5617,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5611,c_140])).

tff(c_5729,plain,(
    ! [A_715,B_716,C_717] :
      ( k2_relset_1(A_715,B_716,C_717) = k2_relat_1(C_717)
      | ~ m1_subset_1(C_717,k1_zfmisc_1(k2_zfmisc_1(A_715,B_716))) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_5737,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_5617,c_5729])).

tff(c_5615,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5611,c_155])).

tff(c_5739,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5737,c_5615])).

tff(c_5618,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5611,c_130])).

tff(c_5769,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5739,c_5618])).

tff(c_5764,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5739,c_5737])).

tff(c_76,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_5767,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5739,c_5617])).

tff(c_6238,plain,(
    ! [A_811,B_812,C_813] :
      ( k2_tops_2(A_811,B_812,C_813) = k2_funct_1(C_813)
      | ~ v2_funct_1(C_813)
      | k2_relset_1(A_811,B_812,C_813) != B_812
      | ~ m1_subset_1(C_813,k1_zfmisc_1(k2_zfmisc_1(A_811,B_812)))
      | ~ v1_funct_2(C_813,A_811,B_812)
      | ~ v1_funct_1(C_813) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_6245,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_5767,c_6238])).

tff(c_6253,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_5769,c_5764,c_76,c_6245])).

tff(c_325,plain,(
    ! [A_109,B_110,C_111] :
      ( k2_relset_1(A_109,B_110,C_111) = k2_relat_1(C_111)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_333,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_140,c_325])).

tff(c_335,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_155])).

tff(c_352,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_335,c_70])).

tff(c_356,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_352])).

tff(c_357,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_356])).

tff(c_220,plain,(
    ! [C_85,A_86,B_87] :
      ( v4_relat_1(C_85,A_86)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_228,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_140,c_220])).

tff(c_274,plain,(
    ! [B_96,A_97] :
      ( k1_relat_1(B_96) = A_97
      | ~ v1_partfun1(B_96,A_97)
      | ~ v4_relat_1(B_96,A_97)
      | ~ v1_relat_1(B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_280,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_228,c_274])).

tff(c_286,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_280])).

tff(c_287,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_286])).

tff(c_347,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_130])).

tff(c_346,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_140])).

tff(c_584,plain,(
    ! [C_139,A_140,B_141] :
      ( v1_partfun1(C_139,A_140)
      | ~ v1_funct_2(C_139,A_140,B_141)
      | ~ v1_funct_1(C_139)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141)))
      | v1_xboole_0(B_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_591,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_346,c_584])).

tff(c_599,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_347,c_591])).

tff(c_601,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_357,c_287,c_599])).

tff(c_602,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_286])).

tff(c_608,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_602,c_140])).

tff(c_679,plain,(
    ! [A_142,B_143,C_144] :
      ( k2_relset_1(A_142,B_143,C_144) = k2_relat_1(C_144)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(A_142,B_143))) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_687,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_608,c_679])).

tff(c_606,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_602,c_155])).

tff(c_693,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_687,c_606])).

tff(c_609,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_602,c_130])).

tff(c_701,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_693,c_609])).

tff(c_698,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_693,c_687])).

tff(c_699,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_693,c_608])).

tff(c_1302,plain,(
    ! [A_252,B_253,C_254] :
      ( k2_tops_2(A_252,B_253,C_254) = k2_funct_1(C_254)
      | ~ v2_funct_1(C_254)
      | k2_relset_1(A_252,B_253,C_254) != B_253
      | ~ m1_subset_1(C_254,k1_zfmisc_1(k2_zfmisc_1(A_252,B_253)))
      | ~ v1_funct_2(C_254,A_252,B_253)
      | ~ v1_funct_1(C_254) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_1313,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_699,c_1302])).

tff(c_1322,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_701,c_698,c_76,c_1313])).

tff(c_74,plain,
    ( k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_205,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_120,c_119,c_119,c_120,c_120,c_119,c_119,c_74])).

tff(c_206,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_205])).

tff(c_604,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_602,c_602,c_206])).

tff(c_857,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_693,c_693,c_693,c_604])).

tff(c_1324,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1322,c_857])).

tff(c_24,plain,(
    ! [A_12] :
      ( v1_relat_1(k2_funct_1(A_12))
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_805,plain,(
    ! [B_156,A_157] :
      ( k9_relat_1(k2_funct_1(B_156),A_157) = k10_relat_1(B_156,A_157)
      | ~ v2_funct_1(B_156)
      | ~ v1_funct_1(B_156)
      | ~ v1_relat_1(B_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_16,plain,(
    ! [A_10] :
      ( k9_relat_1(A_10,k1_relat_1(A_10)) = k2_relat_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1408,plain,(
    ! [B_268] :
      ( k10_relat_1(B_268,k1_relat_1(k2_funct_1(B_268))) = k2_relat_1(k2_funct_1(B_268))
      | ~ v1_relat_1(k2_funct_1(B_268))
      | ~ v2_funct_1(B_268)
      | ~ v1_funct_1(B_268)
      | ~ v1_relat_1(B_268) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_805,c_16])).

tff(c_871,plain,(
    ! [A_165,B_166,C_167,D_168] :
      ( k8_relset_1(A_165,B_166,C_167,D_168) = k10_relat_1(C_167,D_168)
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(A_165,B_166))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_877,plain,(
    ! [D_168] : k8_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3',D_168) = k10_relat_1('#skF_3',D_168) ),
    inference(resolution,[status(thm)],[c_699,c_871])).

tff(c_888,plain,(
    ! [A_170,B_171,C_172,D_173] :
      ( m1_subset_1(k8_relset_1(A_170,B_171,C_172,D_173),k1_zfmisc_1(A_170))
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(A_170,B_171))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_916,plain,(
    ! [D_168] :
      ( m1_subset_1(k10_relat_1('#skF_3',D_168),k1_zfmisc_1(k1_relat_1('#skF_3')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_877,c_888])).

tff(c_926,plain,(
    ! [D_174] : m1_subset_1(k10_relat_1('#skF_3',D_174),k1_zfmisc_1(k1_relat_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_699,c_916])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_934,plain,(
    ! [D_174] : r1_tarski(k10_relat_1('#skF_3',D_174),k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_926,c_8])).

tff(c_1451,plain,
    ( r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1408,c_934])).

tff(c_1482,plain,
    ( r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_84,c_76,c_1451])).

tff(c_1486,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1482])).

tff(c_1489,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_1486])).

tff(c_1493,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_84,c_1489])).

tff(c_1495,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1482])).

tff(c_1336,plain,(
    ! [C_260,B_261,A_262] :
      ( m1_subset_1(k2_funct_1(C_260),k1_zfmisc_1(k2_zfmisc_1(B_261,A_262)))
      | k2_relset_1(A_262,B_261,C_260) != B_261
      | ~ v2_funct_1(C_260)
      | ~ m1_subset_1(C_260,k1_zfmisc_1(k2_zfmisc_1(A_262,B_261)))
      | ~ v1_funct_2(C_260,A_262,B_261)
      | ~ v1_funct_1(C_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_44,plain,(
    ! [C_23,A_21,B_22] :
      ( v4_relat_1(C_23,A_21)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_2358,plain,(
    ! [C_371,B_372,A_373] :
      ( v4_relat_1(k2_funct_1(C_371),B_372)
      | k2_relset_1(A_373,B_372,C_371) != B_372
      | ~ v2_funct_1(C_371)
      | ~ m1_subset_1(C_371,k1_zfmisc_1(k2_zfmisc_1(A_373,B_372)))
      | ~ v1_funct_2(C_371,A_373,B_372)
      | ~ v1_funct_1(C_371) ) ),
    inference(resolution,[status(thm)],[c_1336,c_44])).

tff(c_2376,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_699,c_2358])).

tff(c_2388,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_701,c_76,c_698,c_2376])).

tff(c_60,plain,(
    ! [B_43,A_42] :
      ( k1_relat_1(B_43) = A_42
      | ~ v1_partfun1(B_43,A_42)
      | ~ v4_relat_1(B_43,A_42)
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_2392,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2388,c_60])).

tff(c_2395,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1495,c_2392])).

tff(c_2396,plain,(
    ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2395])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1125,plain,(
    ! [C_222,A_223,B_224] :
      ( v1_funct_1(k2_funct_1(C_222))
      | k2_relset_1(A_223,B_224,C_222) != B_224
      | ~ v2_funct_1(C_222)
      | ~ m1_subset_1(C_222,k1_zfmisc_1(k2_zfmisc_1(A_223,B_224)))
      | ~ v1_funct_2(C_222,A_223,B_224)
      | ~ v1_funct_1(C_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_1132,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_699,c_1125])).

tff(c_1140,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_701,c_76,c_698,c_1132])).

tff(c_26,plain,(
    ! [A_13] :
      ( v2_funct_1(k2_funct_1(A_13))
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_40,plain,(
    ! [A_20] :
      ( k2_funct_1(k2_funct_1(A_20)) = A_20
      | ~ v2_funct_1(A_20)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2023,plain,(
    ! [A_343,A_344] :
      ( k10_relat_1(k2_funct_1(A_343),A_344) = k9_relat_1(A_343,A_344)
      | ~ v2_funct_1(k2_funct_1(A_343))
      | ~ v1_funct_1(k2_funct_1(A_343))
      | ~ v1_relat_1(k2_funct_1(A_343))
      | ~ v2_funct_1(A_343)
      | ~ v1_funct_1(A_343)
      | ~ v1_relat_1(A_343) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_805])).

tff(c_2100,plain,(
    ! [A_360,A_361] :
      ( k10_relat_1(k2_funct_1(A_360),A_361) = k9_relat_1(A_360,A_361)
      | ~ v1_funct_1(k2_funct_1(A_360))
      | ~ v1_relat_1(k2_funct_1(A_360))
      | ~ v2_funct_1(A_360)
      | ~ v1_funct_1(A_360)
      | ~ v1_relat_1(A_360) ) ),
    inference(resolution,[status(thm)],[c_26,c_2023])).

tff(c_2102,plain,(
    ! [A_361] :
      ( k10_relat_1(k2_funct_1('#skF_3'),A_361) = k9_relat_1('#skF_3',A_361)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1495,c_2100])).

tff(c_2154,plain,(
    ! [A_363] : k10_relat_1(k2_funct_1('#skF_3'),A_363) = k9_relat_1('#skF_3',A_363) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_84,c_76,c_1140,c_2102])).

tff(c_812,plain,(
    ! [B_156] :
      ( k10_relat_1(B_156,k1_relat_1(k2_funct_1(B_156))) = k2_relat_1(k2_funct_1(B_156))
      | ~ v1_relat_1(k2_funct_1(B_156))
      | ~ v2_funct_1(B_156)
      | ~ v1_funct_1(B_156)
      | ~ v1_relat_1(B_156) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_805,c_16])).

tff(c_2161,plain,
    ( k9_relat_1('#skF_3',k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) = k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2154,c_812])).

tff(c_2171,plain,
    ( k9_relat_1('#skF_3',k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) = k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1495,c_1140,c_2161])).

tff(c_2219,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2171])).

tff(c_2222,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_2219])).

tff(c_2226,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_84,c_76,c_2222])).

tff(c_2228,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2171])).

tff(c_20,plain,(
    ! [A_11] : k2_relat_1(k6_relat_1(A_11)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_36,plain,(
    ! [A_19] :
      ( k5_relat_1(k2_funct_1(A_19),A_19) = k6_relat_1(k2_relat_1(A_19))
      | ~ v2_funct_1(A_19)
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_858,plain,(
    ! [A_164] :
      ( k5_relat_1(A_164,k2_funct_1(A_164)) = k6_relat_1(k1_relat_1(A_164))
      | ~ v2_funct_1(A_164)
      | ~ v1_funct_1(A_164)
      | ~ v1_relat_1(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2111,plain,(
    ! [A_362] :
      ( k6_relat_1(k1_relat_1(k2_funct_1(A_362))) = k5_relat_1(k2_funct_1(A_362),A_362)
      | ~ v2_funct_1(k2_funct_1(A_362))
      | ~ v1_funct_1(k2_funct_1(A_362))
      | ~ v1_relat_1(k2_funct_1(A_362))
      | ~ v2_funct_1(A_362)
      | ~ v1_funct_1(A_362)
      | ~ v1_relat_1(A_362) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_858])).

tff(c_2987,plain,(
    ! [A_444] :
      ( k2_relat_1(k5_relat_1(k2_funct_1(A_444),A_444)) = k1_relat_1(k2_funct_1(A_444))
      | ~ v2_funct_1(k2_funct_1(A_444))
      | ~ v1_funct_1(k2_funct_1(A_444))
      | ~ v1_relat_1(k2_funct_1(A_444))
      | ~ v2_funct_1(A_444)
      | ~ v1_funct_1(A_444)
      | ~ v1_relat_1(A_444) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2111,c_20])).

tff(c_3011,plain,(
    ! [A_19] :
      ( k2_relat_1(k6_relat_1(k2_relat_1(A_19))) = k1_relat_1(k2_funct_1(A_19))
      | ~ v2_funct_1(k2_funct_1(A_19))
      | ~ v1_funct_1(k2_funct_1(A_19))
      | ~ v1_relat_1(k2_funct_1(A_19))
      | ~ v2_funct_1(A_19)
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19)
      | ~ v2_funct_1(A_19)
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_2987])).

tff(c_3592,plain,(
    ! [A_496] :
      ( k1_relat_1(k2_funct_1(A_496)) = k2_relat_1(A_496)
      | ~ v2_funct_1(k2_funct_1(A_496))
      | ~ v1_funct_1(k2_funct_1(A_496))
      | ~ v1_relat_1(k2_funct_1(A_496))
      | ~ v2_funct_1(A_496)
      | ~ v1_funct_1(A_496)
      | ~ v1_relat_1(A_496)
      | ~ v2_funct_1(A_496)
      | ~ v1_funct_1(A_496)
      | ~ v1_relat_1(A_496) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_3011])).

tff(c_3595,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2228,c_3592])).

tff(c_3604,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_84,c_76,c_1495,c_1140,c_3595])).

tff(c_34,plain,(
    ! [A_16,B_18] :
      ( r1_tarski(k1_relat_1(A_16),k2_relat_1(B_18))
      | ~ v2_funct_1(A_16)
      | k2_relat_1(k5_relat_1(B_18,A_16)) != k2_relat_1(A_16)
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1494,plain,(
    r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1482])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1519,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_3'),k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_1494,c_2])).

tff(c_1531,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_1519])).

tff(c_1537,plain,
    ( ~ v2_funct_1('#skF_3')
    | k2_relat_1(k5_relat_1(k2_funct_1('#skF_3'),'#skF_3')) != k2_relat_1('#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_1531])).

tff(c_1540,plain,(
    k2_relat_1(k5_relat_1(k2_funct_1('#skF_3'),'#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_84,c_1495,c_1140,c_76,c_1537])).

tff(c_1543,plain,
    ( k2_relat_1(k6_relat_1(k2_relat_1('#skF_3'))) != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1540])).

tff(c_1546,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_84,c_76,c_20,c_1543])).

tff(c_1547,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1519])).

tff(c_2227,plain,
    ( ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k9_relat_1('#skF_3',k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) = k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_2171])).

tff(c_2229,plain,(
    ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_2227])).

tff(c_2232,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_2229])).

tff(c_2238,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_84,c_76,c_182,c_2232])).

tff(c_2240,plain,(
    v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_2227])).

tff(c_18,plain,(
    ! [A_11] : k1_relat_1(k6_relat_1(A_11)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1555,plain,(
    ! [A_16] :
      ( r1_tarski(k1_relat_1(A_16),k1_relat_1('#skF_3'))
      | ~ v2_funct_1(A_16)
      | k2_relat_1(k5_relat_1(k2_funct_1('#skF_3'),A_16)) != k2_relat_1(A_16)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1547,c_34])).

tff(c_1600,plain,(
    ! [A_276] :
      ( r1_tarski(k1_relat_1(A_276),k1_relat_1('#skF_3'))
      | ~ v2_funct_1(A_276)
      | k2_relat_1(k5_relat_1(k2_funct_1('#skF_3'),A_276)) != k2_relat_1(A_276)
      | ~ v1_funct_1(A_276)
      | ~ v1_relat_1(A_276) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1495,c_1140,c_1555])).

tff(c_1608,plain,(
    ! [A_11] :
      ( r1_tarski(A_11,k1_relat_1('#skF_3'))
      | ~ v2_funct_1(k6_relat_1(A_11))
      | k2_relat_1(k5_relat_1(k2_funct_1('#skF_3'),k6_relat_1(A_11))) != k2_relat_1(k6_relat_1(A_11))
      | ~ v1_funct_1(k6_relat_1(A_11))
      | ~ v1_relat_1(k6_relat_1(A_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1600])).

tff(c_1611,plain,(
    ! [A_11] :
      ( r1_tarski(A_11,k1_relat_1('#skF_3'))
      | ~ v2_funct_1(k6_relat_1(A_11))
      | k2_relat_1(k5_relat_1(k2_funct_1('#skF_3'),k6_relat_1(A_11))) != A_11
      | ~ v1_funct_1(k6_relat_1(A_11))
      | ~ v1_relat_1(k6_relat_1(A_11)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1608])).

tff(c_2397,plain,(
    ! [A_374] :
      ( r1_tarski(k1_relat_1(k2_funct_1(A_374)),k1_relat_1('#skF_3'))
      | ~ v2_funct_1(k6_relat_1(k1_relat_1(k2_funct_1(A_374))))
      | k2_relat_1(k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1(k2_funct_1(A_374),A_374))) != k1_relat_1(k2_funct_1(A_374))
      | ~ v1_funct_1(k6_relat_1(k1_relat_1(k2_funct_1(A_374))))
      | ~ v1_relat_1(k6_relat_1(k1_relat_1(k2_funct_1(A_374))))
      | ~ v2_funct_1(k2_funct_1(A_374))
      | ~ v1_funct_1(k2_funct_1(A_374))
      | ~ v1_relat_1(k2_funct_1(A_374))
      | ~ v2_funct_1(A_374)
      | ~ v1_funct_1(A_374)
      | ~ v1_relat_1(A_374) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2111,c_1611])).

tff(c_2791,plain,(
    ! [A_434] :
      ( r1_tarski(k1_relat_1(k2_funct_1(A_434)),k1_relat_1('#skF_3'))
      | ~ v2_funct_1(k6_relat_1(k1_relat_1(k2_funct_1(A_434))))
      | k2_relat_1(k5_relat_1(k2_funct_1('#skF_3'),k6_relat_1(k2_relat_1(A_434)))) != k1_relat_1(k2_funct_1(A_434))
      | ~ v1_funct_1(k6_relat_1(k1_relat_1(k2_funct_1(A_434))))
      | ~ v1_relat_1(k6_relat_1(k1_relat_1(k2_funct_1(A_434))))
      | ~ v2_funct_1(k2_funct_1(A_434))
      | ~ v1_funct_1(k2_funct_1(A_434))
      | ~ v1_relat_1(k2_funct_1(A_434))
      | ~ v2_funct_1(A_434)
      | ~ v1_funct_1(A_434)
      | ~ v1_relat_1(A_434)
      | ~ v2_funct_1(A_434)
      | ~ v1_funct_1(A_434)
      | ~ v1_relat_1(A_434) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_2397])).

tff(c_2797,plain,
    ( r1_tarski(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))),k1_relat_1('#skF_3'))
    | ~ v2_funct_1(k6_relat_1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))))
    | k2_relat_1(k5_relat_1(k2_funct_1('#skF_3'),k6_relat_1(k1_relat_1('#skF_3')))) != k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k6_relat_1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))))
    | ~ v1_relat_1(k6_relat_1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1547,c_2791])).

tff(c_2804,plain,
    ( r1_tarski(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))),k1_relat_1('#skF_3'))
    | ~ v2_funct_1(k6_relat_1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))))
    | k2_relat_1(k5_relat_1(k2_funct_1('#skF_3'),k6_relat_1(k1_relat_1('#skF_3')))) != k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k6_relat_1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))))
    | ~ v1_relat_1(k6_relat_1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1495,c_1140,c_2228,c_1495,c_1140,c_2228,c_2240,c_2797])).

tff(c_3019,plain,(
    ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_2804])).

tff(c_3022,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_3019])).

tff(c_3028,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_84,c_76,c_84,c_3022])).

tff(c_3030,plain,(
    v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_2804])).

tff(c_2239,plain,(
    k9_relat_1('#skF_3',k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) = k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_2227])).

tff(c_2282,plain,
    ( k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) = k9_relat_1('#skF_3',k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_2239])).

tff(c_2286,plain,(
    k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) = k9_relat_1('#skF_3',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_84,c_76,c_2282])).

tff(c_2295,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_2286])).

tff(c_2301,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_84,c_76,c_2295])).

tff(c_2315,plain,(
    k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2301,c_2286])).

tff(c_2335,plain,(
    ! [A_16] :
      ( r1_tarski(k1_relat_1(A_16),k2_relat_1('#skF_3'))
      | ~ v2_funct_1(A_16)
      | k2_relat_1(k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),A_16)) != k2_relat_1(A_16)
      | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
      | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2315,c_34])).

tff(c_2342,plain,(
    ! [A_16] :
      ( r1_tarski(k1_relat_1(A_16),k2_relat_1('#skF_3'))
      | ~ v2_funct_1(A_16)
      | k2_relat_1(k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),A_16)) != k2_relat_1(A_16)
      | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2240,c_2335])).

tff(c_3111,plain,(
    ! [A_447] :
      ( r1_tarski(k1_relat_1(A_447),k2_relat_1('#skF_3'))
      | ~ v2_funct_1(A_447)
      | k2_relat_1(k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),A_447)) != k2_relat_1(A_447)
      | ~ v1_funct_1(A_447)
      | ~ v1_relat_1(A_447) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3030,c_2342])).

tff(c_3135,plain,
    ( r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),k2_relat_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relat_1(k6_relat_1(k2_relat_1(k2_funct_1('#skF_3')))) != k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_3111])).

tff(c_3151,plain,(
    r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1495,c_1140,c_2228,c_1495,c_1140,c_20,c_1547,c_1547,c_2228,c_3135])).

tff(c_3217,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ r1_tarski(k2_relat_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_3151,c_2])).

tff(c_3225,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_3217])).

tff(c_3606,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3604,c_3225])).

tff(c_3611,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3606])).

tff(c_3612,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_3217])).

tff(c_58,plain,(
    ! [B_43] :
      ( v1_partfun1(B_43,k1_relat_1(B_43))
      | ~ v4_relat_1(B_43,k1_relat_1(B_43))
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_3635,plain,
    ( v1_partfun1(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')))
    | ~ v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3612,c_58])).

tff(c_3652,plain,(
    v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1495,c_2388,c_3612,c_3635])).

tff(c_3654,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2396,c_3652])).

tff(c_3655,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_2395])).

tff(c_48,plain,(
    ! [A_28,B_29,C_30] :
      ( k1_relset_1(A_28,B_29,C_30) = k1_relat_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_5073,plain,(
    ! [B_625,A_626,C_627] :
      ( k1_relset_1(B_625,A_626,k2_funct_1(C_627)) = k1_relat_1(k2_funct_1(C_627))
      | k2_relset_1(A_626,B_625,C_627) != B_625
      | ~ v2_funct_1(C_627)
      | ~ m1_subset_1(C_627,k1_zfmisc_1(k2_zfmisc_1(A_626,B_625)))
      | ~ v1_funct_2(C_627,A_626,B_625)
      | ~ v1_funct_1(C_627) ) ),
    inference(resolution,[status(thm)],[c_1336,c_48])).

tff(c_5095,plain,
    ( k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_699,c_5073])).

tff(c_5108,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_701,c_76,c_698,c_3655,c_5095])).

tff(c_5110,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1324,c_5108])).

tff(c_5111,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_205])).

tff(c_5707,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5611,c_5611,c_5611,c_5111])).

tff(c_5765,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5739,c_5739,c_5707])).

tff(c_6320,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6253,c_5765])).

tff(c_5744,plain,(
    ! [B_718,A_719] :
      ( k9_relat_1(k2_funct_1(B_718),A_719) = k10_relat_1(B_718,A_719)
      | ~ v2_funct_1(B_718)
      | ~ v1_funct_1(B_718)
      | ~ v1_relat_1(B_718) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_6426,plain,(
    ! [B_825] :
      ( k10_relat_1(B_825,k1_relat_1(k2_funct_1(B_825))) = k2_relat_1(k2_funct_1(B_825))
      | ~ v2_funct_1(B_825)
      | ~ v1_funct_1(B_825)
      | ~ v1_relat_1(B_825)
      | ~ v1_relat_1(k2_funct_1(B_825)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_5744])).

tff(c_5900,plain,(
    ! [A_727,B_728,C_729,D_730] :
      ( k8_relset_1(A_727,B_728,C_729,D_730) = k10_relat_1(C_729,D_730)
      | ~ m1_subset_1(C_729,k1_zfmisc_1(k2_zfmisc_1(A_727,B_728))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_5906,plain,(
    ! [D_730] : k8_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3',D_730) = k10_relat_1('#skF_3',D_730) ),
    inference(resolution,[status(thm)],[c_5767,c_5900])).

tff(c_5936,plain,(
    ! [A_739,B_740,C_741,D_742] :
      ( m1_subset_1(k8_relset_1(A_739,B_740,C_741,D_742),k1_zfmisc_1(A_739))
      | ~ m1_subset_1(C_741,k1_zfmisc_1(k2_zfmisc_1(A_739,B_740))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_5967,plain,(
    ! [D_730] :
      ( m1_subset_1(k10_relat_1('#skF_3',D_730),k1_zfmisc_1(k1_relat_1('#skF_3')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5906,c_5936])).

tff(c_5976,plain,(
    ! [D_730] : m1_subset_1(k10_relat_1('#skF_3',D_730),k1_zfmisc_1(k1_relat_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5767,c_5967])).

tff(c_6473,plain,
    ( m1_subset_1(k2_relat_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k1_relat_1('#skF_3')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6426,c_5976])).

tff(c_6502,plain,
    ( m1_subset_1(k2_relat_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k1_relat_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_84,c_76,c_6473])).

tff(c_6514,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_6502])).

tff(c_6517,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_6514])).

tff(c_6521,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_84,c_6517])).

tff(c_6523,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_6502])).

tff(c_6142,plain,(
    ! [C_780,A_781,B_782] :
      ( v1_funct_1(k2_funct_1(C_780))
      | k2_relset_1(A_781,B_782,C_780) != B_782
      | ~ v2_funct_1(C_780)
      | ~ m1_subset_1(C_780,k1_zfmisc_1(k2_zfmisc_1(A_781,B_782)))
      | ~ v1_funct_2(C_780,A_781,B_782)
      | ~ v1_funct_1(C_780) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_6149,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_5767,c_6142])).

tff(c_6157,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_5769,c_76,c_5764,c_6149])).

tff(c_5977,plain,(
    ! [D_743] : m1_subset_1(k10_relat_1('#skF_3',D_743),k1_zfmisc_1(k1_relat_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5767,c_5967])).

tff(c_5985,plain,(
    ! [D_743] : r1_tarski(k10_relat_1('#skF_3',D_743),k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_5977,c_8])).

tff(c_6469,plain,
    ( r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6426,c_5985])).

tff(c_6500,plain,
    ( r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_84,c_76,c_6469])).

tff(c_6504,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_6500])).

tff(c_6507,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_6504])).

tff(c_6511,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_84,c_6507])).

tff(c_6512,plain,(
    r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_6500])).

tff(c_6531,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_3'),k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_6512,c_2])).

tff(c_6558,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_6531])).

tff(c_6561,plain,
    ( ~ v2_funct_1('#skF_3')
    | k2_relat_1(k5_relat_1(k2_funct_1('#skF_3'),'#skF_3')) != k2_relat_1('#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_6558])).

tff(c_6564,plain,(
    k2_relat_1(k5_relat_1(k2_funct_1('#skF_3'),'#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_84,c_6523,c_6157,c_76,c_6561])).

tff(c_6567,plain,
    ( k2_relat_1(k6_relat_1(k2_relat_1('#skF_3'))) != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_6564])).

tff(c_6570,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_84,c_76,c_20,c_6567])).

tff(c_6571,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_6531])).

tff(c_6371,plain,(
    ! [C_822,B_823,A_824] :
      ( m1_subset_1(k2_funct_1(C_822),k1_zfmisc_1(k2_zfmisc_1(B_823,A_824)))
      | k2_relset_1(A_824,B_823,C_822) != B_823
      | ~ v2_funct_1(C_822)
      | ~ m1_subset_1(C_822,k1_zfmisc_1(k2_zfmisc_1(A_824,B_823)))
      | ~ v1_funct_2(C_822,A_824,B_823)
      | ~ v1_funct_1(C_822) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_50,plain,(
    ! [A_31,B_32,C_33] :
      ( k2_relset_1(A_31,B_32,C_33) = k2_relat_1(C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_9017,plain,(
    ! [B_1065,A_1066,C_1067] :
      ( k2_relset_1(B_1065,A_1066,k2_funct_1(C_1067)) = k2_relat_1(k2_funct_1(C_1067))
      | k2_relset_1(A_1066,B_1065,C_1067) != B_1065
      | ~ v2_funct_1(C_1067)
      | ~ m1_subset_1(C_1067,k1_zfmisc_1(k2_zfmisc_1(A_1066,B_1065)))
      | ~ v1_funct_2(C_1067,A_1066,B_1065)
      | ~ v1_funct_1(C_1067) ) ),
    inference(resolution,[status(thm)],[c_6371,c_50])).

tff(c_9039,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_5767,c_9017])).

tff(c_9052,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_5769,c_76,c_5764,c_6571,c_9039])).

tff(c_9054,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6320,c_9052])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:58:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.45/3.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.45/3.17  
% 8.45/3.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.45/3.17  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k6_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 8.45/3.17  
% 8.45/3.17  %Foreground sorts:
% 8.45/3.17  
% 8.45/3.17  
% 8.45/3.17  %Background operators:
% 8.45/3.17  
% 8.45/3.17  
% 8.45/3.17  %Foreground operators:
% 8.45/3.17  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.45/3.17  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.45/3.17  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.45/3.17  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 8.45/3.17  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.45/3.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.45/3.17  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 8.45/3.17  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 8.45/3.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.45/3.17  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.45/3.17  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 8.45/3.17  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.45/3.17  tff('#skF_2', type, '#skF_2': $i).
% 8.45/3.17  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 8.45/3.17  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 8.45/3.17  tff('#skF_3', type, '#skF_3': $i).
% 8.45/3.17  tff('#skF_1', type, '#skF_1': $i).
% 8.45/3.17  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.45/3.17  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.45/3.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.45/3.17  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 8.45/3.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.45/3.17  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 8.45/3.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.45/3.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.45/3.17  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 8.45/3.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.45/3.17  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.45/3.17  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.45/3.17  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 8.45/3.17  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.45/3.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.45/3.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.45/3.17  
% 8.79/3.21  tff(f_221, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_2)).
% 8.79/3.21  tff(f_177, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 8.79/3.21  tff(f_131, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.79/3.21  tff(f_185, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_struct_0)).
% 8.79/3.21  tff(f_44, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.79/3.21  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 8.79/3.21  tff(f_119, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.79/3.21  tff(f_157, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 8.79/3.21  tff(f_149, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 8.79/3.21  tff(f_197, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 8.79/3.21  tff(f_60, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 8.79/3.21  tff(f_80, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_funct_1)).
% 8.79/3.21  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 8.79/3.21  tff(f_135, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 8.79/3.21  tff(f_123, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k8_relset_1(A, B, C, D), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relset_1)).
% 8.79/3.21  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.79/3.21  tff(f_173, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 8.79/3.21  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.79/3.21  tff(f_72, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_funct_1)).
% 8.79/3.21  tff(f_113, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 8.79/3.21  tff(f_52, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 8.79/3.21  tff(f_105, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 8.79/3.21  tff(f_95, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A)) & v2_funct_1(A)) => r1_tarski(k1_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_funct_1)).
% 8.79/3.21  tff(f_127, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.79/3.21  tff(c_84, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_221])).
% 8.79/3.21  tff(c_88, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_221])).
% 8.79/3.21  tff(c_86, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_221])).
% 8.79/3.21  tff(c_90, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_221])).
% 8.79/3.21  tff(c_112, plain, (![A_61]: (u1_struct_0(A_61)=k2_struct_0(A_61) | ~l1_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_177])).
% 8.79/3.21  tff(c_120, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_90, c_112])).
% 8.79/3.21  tff(c_119, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_86, c_112])).
% 8.79/3.21  tff(c_80, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_221])).
% 8.79/3.21  tff(c_140, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_119, c_80])).
% 8.79/3.21  tff(c_5214, plain, (![A_653, B_654, C_655]: (k2_relset_1(A_653, B_654, C_655)=k2_relat_1(C_655) | ~m1_subset_1(C_655, k1_zfmisc_1(k2_zfmisc_1(A_653, B_654))))), inference(cnfTransformation, [status(thm)], [f_131])).
% 8.79/3.21  tff(c_5222, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_140, c_5214])).
% 8.79/3.21  tff(c_78, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_221])).
% 8.79/3.21  tff(c_155, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_119, c_78])).
% 8.79/3.21  tff(c_5224, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5222, c_155])).
% 8.79/3.21  tff(c_70, plain, (![A_48]: (~v1_xboole_0(k2_struct_0(A_48)) | ~l1_struct_0(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_185])).
% 8.79/3.21  tff(c_5241, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5224, c_70])).
% 8.79/3.21  tff(c_5245, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_5241])).
% 8.79/3.21  tff(c_5246, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_88, c_5245])).
% 8.79/3.21  tff(c_14, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.79/3.21  tff(c_173, plain, (![B_72, A_73]: (v1_relat_1(B_72) | ~m1_subset_1(B_72, k1_zfmisc_1(A_73)) | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.79/3.21  tff(c_176, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_140, c_173])).
% 8.79/3.21  tff(c_182, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_176])).
% 8.79/3.21  tff(c_5130, plain, (![C_634, A_635, B_636]: (v4_relat_1(C_634, A_635) | ~m1_subset_1(C_634, k1_zfmisc_1(k2_zfmisc_1(A_635, B_636))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 8.79/3.21  tff(c_5138, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_140, c_5130])).
% 8.79/3.21  tff(c_5184, plain, (![B_645, A_646]: (k1_relat_1(B_645)=A_646 | ~v1_partfun1(B_645, A_646) | ~v4_relat_1(B_645, A_646) | ~v1_relat_1(B_645))), inference(cnfTransformation, [status(thm)], [f_157])).
% 8.79/3.21  tff(c_5190, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_5138, c_5184])).
% 8.79/3.21  tff(c_5196, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_5190])).
% 8.79/3.21  tff(c_5197, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_5196])).
% 8.79/3.21  tff(c_82, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_221])).
% 8.79/3.21  tff(c_121, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_82])).
% 8.79/3.21  tff(c_130, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_121])).
% 8.79/3.21  tff(c_5236, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5224, c_130])).
% 8.79/3.21  tff(c_5235, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_5224, c_140])).
% 8.79/3.21  tff(c_5593, plain, (![C_701, A_702, B_703]: (v1_partfun1(C_701, A_702) | ~v1_funct_2(C_701, A_702, B_703) | ~v1_funct_1(C_701) | ~m1_subset_1(C_701, k1_zfmisc_1(k2_zfmisc_1(A_702, B_703))) | v1_xboole_0(B_703))), inference(cnfTransformation, [status(thm)], [f_149])).
% 8.79/3.21  tff(c_5600, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_5235, c_5593])).
% 8.79/3.21  tff(c_5608, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_5236, c_5600])).
% 8.79/3.21  tff(c_5610, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5246, c_5197, c_5608])).
% 8.79/3.21  tff(c_5611, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_5196])).
% 8.79/3.21  tff(c_5617, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_5611, c_140])).
% 8.79/3.21  tff(c_5729, plain, (![A_715, B_716, C_717]: (k2_relset_1(A_715, B_716, C_717)=k2_relat_1(C_717) | ~m1_subset_1(C_717, k1_zfmisc_1(k2_zfmisc_1(A_715, B_716))))), inference(cnfTransformation, [status(thm)], [f_131])).
% 8.79/3.21  tff(c_5737, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_5617, c_5729])).
% 8.79/3.21  tff(c_5615, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5611, c_155])).
% 8.79/3.21  tff(c_5739, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5737, c_5615])).
% 8.79/3.21  tff(c_5618, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_5611, c_130])).
% 8.79/3.21  tff(c_5769, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5739, c_5618])).
% 8.79/3.21  tff(c_5764, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5739, c_5737])).
% 8.79/3.21  tff(c_76, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_221])).
% 8.79/3.21  tff(c_5767, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_5739, c_5617])).
% 8.79/3.21  tff(c_6238, plain, (![A_811, B_812, C_813]: (k2_tops_2(A_811, B_812, C_813)=k2_funct_1(C_813) | ~v2_funct_1(C_813) | k2_relset_1(A_811, B_812, C_813)!=B_812 | ~m1_subset_1(C_813, k1_zfmisc_1(k2_zfmisc_1(A_811, B_812))) | ~v1_funct_2(C_813, A_811, B_812) | ~v1_funct_1(C_813))), inference(cnfTransformation, [status(thm)], [f_197])).
% 8.79/3.21  tff(c_6245, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_5767, c_6238])).
% 8.79/3.21  tff(c_6253, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_5769, c_5764, c_76, c_6245])).
% 8.79/3.21  tff(c_325, plain, (![A_109, B_110, C_111]: (k2_relset_1(A_109, B_110, C_111)=k2_relat_1(C_111) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))))), inference(cnfTransformation, [status(thm)], [f_131])).
% 8.79/3.21  tff(c_333, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_140, c_325])).
% 8.79/3.21  tff(c_335, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_333, c_155])).
% 8.79/3.21  tff(c_352, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_335, c_70])).
% 8.79/3.21  tff(c_356, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_352])).
% 8.79/3.21  tff(c_357, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_88, c_356])).
% 8.79/3.21  tff(c_220, plain, (![C_85, A_86, B_87]: (v4_relat_1(C_85, A_86) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 8.79/3.21  tff(c_228, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_140, c_220])).
% 8.79/3.21  tff(c_274, plain, (![B_96, A_97]: (k1_relat_1(B_96)=A_97 | ~v1_partfun1(B_96, A_97) | ~v4_relat_1(B_96, A_97) | ~v1_relat_1(B_96))), inference(cnfTransformation, [status(thm)], [f_157])).
% 8.79/3.21  tff(c_280, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_228, c_274])).
% 8.79/3.21  tff(c_286, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_280])).
% 8.79/3.21  tff(c_287, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_286])).
% 8.79/3.21  tff(c_347, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_335, c_130])).
% 8.79/3.21  tff(c_346, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_335, c_140])).
% 8.79/3.21  tff(c_584, plain, (![C_139, A_140, B_141]: (v1_partfun1(C_139, A_140) | ~v1_funct_2(C_139, A_140, B_141) | ~v1_funct_1(C_139) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))) | v1_xboole_0(B_141))), inference(cnfTransformation, [status(thm)], [f_149])).
% 8.79/3.21  tff(c_591, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_346, c_584])).
% 8.79/3.21  tff(c_599, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_347, c_591])).
% 8.79/3.21  tff(c_601, plain, $false, inference(negUnitSimplification, [status(thm)], [c_357, c_287, c_599])).
% 8.79/3.21  tff(c_602, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_286])).
% 8.79/3.21  tff(c_608, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_602, c_140])).
% 8.79/3.21  tff(c_679, plain, (![A_142, B_143, C_144]: (k2_relset_1(A_142, B_143, C_144)=k2_relat_1(C_144) | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(A_142, B_143))))), inference(cnfTransformation, [status(thm)], [f_131])).
% 8.79/3.21  tff(c_687, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_608, c_679])).
% 8.79/3.21  tff(c_606, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_602, c_155])).
% 8.79/3.21  tff(c_693, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_687, c_606])).
% 8.79/3.21  tff(c_609, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_602, c_130])).
% 8.79/3.21  tff(c_701, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_693, c_609])).
% 8.79/3.21  tff(c_698, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_693, c_687])).
% 8.79/3.21  tff(c_699, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_693, c_608])).
% 8.79/3.21  tff(c_1302, plain, (![A_252, B_253, C_254]: (k2_tops_2(A_252, B_253, C_254)=k2_funct_1(C_254) | ~v2_funct_1(C_254) | k2_relset_1(A_252, B_253, C_254)!=B_253 | ~m1_subset_1(C_254, k1_zfmisc_1(k2_zfmisc_1(A_252, B_253))) | ~v1_funct_2(C_254, A_252, B_253) | ~v1_funct_1(C_254))), inference(cnfTransformation, [status(thm)], [f_197])).
% 8.79/3.21  tff(c_1313, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_699, c_1302])).
% 8.79/3.21  tff(c_1322, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_701, c_698, c_76, c_1313])).
% 8.79/3.21  tff(c_74, plain, (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_221])).
% 8.79/3.21  tff(c_205, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_120, c_119, c_119, c_120, c_120, c_119, c_119, c_74])).
% 8.79/3.21  tff(c_206, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_205])).
% 8.79/3.21  tff(c_604, plain, (k1_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_602, c_602, c_206])).
% 8.79/3.21  tff(c_857, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_693, c_693, c_693, c_604])).
% 8.79/3.21  tff(c_1324, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1322, c_857])).
% 8.79/3.21  tff(c_24, plain, (![A_12]: (v1_relat_1(k2_funct_1(A_12)) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.79/3.21  tff(c_805, plain, (![B_156, A_157]: (k9_relat_1(k2_funct_1(B_156), A_157)=k10_relat_1(B_156, A_157) | ~v2_funct_1(B_156) | ~v1_funct_1(B_156) | ~v1_relat_1(B_156))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.79/3.21  tff(c_16, plain, (![A_10]: (k9_relat_1(A_10, k1_relat_1(A_10))=k2_relat_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 8.79/3.21  tff(c_1408, plain, (![B_268]: (k10_relat_1(B_268, k1_relat_1(k2_funct_1(B_268)))=k2_relat_1(k2_funct_1(B_268)) | ~v1_relat_1(k2_funct_1(B_268)) | ~v2_funct_1(B_268) | ~v1_funct_1(B_268) | ~v1_relat_1(B_268))), inference(superposition, [status(thm), theory('equality')], [c_805, c_16])).
% 8.79/3.21  tff(c_871, plain, (![A_165, B_166, C_167, D_168]: (k8_relset_1(A_165, B_166, C_167, D_168)=k10_relat_1(C_167, D_168) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1(A_165, B_166))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 8.79/3.21  tff(c_877, plain, (![D_168]: (k8_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', D_168)=k10_relat_1('#skF_3', D_168))), inference(resolution, [status(thm)], [c_699, c_871])).
% 8.79/3.21  tff(c_888, plain, (![A_170, B_171, C_172, D_173]: (m1_subset_1(k8_relset_1(A_170, B_171, C_172, D_173), k1_zfmisc_1(A_170)) | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(A_170, B_171))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 8.79/3.21  tff(c_916, plain, (![D_168]: (m1_subset_1(k10_relat_1('#skF_3', D_168), k1_zfmisc_1(k1_relat_1('#skF_3'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))))), inference(superposition, [status(thm), theory('equality')], [c_877, c_888])).
% 8.79/3.21  tff(c_926, plain, (![D_174]: (m1_subset_1(k10_relat_1('#skF_3', D_174), k1_zfmisc_1(k1_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_699, c_916])).
% 8.79/3.21  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.79/3.21  tff(c_934, plain, (![D_174]: (r1_tarski(k10_relat_1('#skF_3', D_174), k1_relat_1('#skF_3')))), inference(resolution, [status(thm)], [c_926, c_8])).
% 8.79/3.21  tff(c_1451, plain, (r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1408, c_934])).
% 8.79/3.21  tff(c_1482, plain, (r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_84, c_76, c_1451])).
% 8.79/3.21  tff(c_1486, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1482])).
% 8.79/3.21  tff(c_1489, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_1486])).
% 8.79/3.21  tff(c_1493, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_182, c_84, c_1489])).
% 8.79/3.21  tff(c_1495, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1482])).
% 8.79/3.21  tff(c_1336, plain, (![C_260, B_261, A_262]: (m1_subset_1(k2_funct_1(C_260), k1_zfmisc_1(k2_zfmisc_1(B_261, A_262))) | k2_relset_1(A_262, B_261, C_260)!=B_261 | ~v2_funct_1(C_260) | ~m1_subset_1(C_260, k1_zfmisc_1(k2_zfmisc_1(A_262, B_261))) | ~v1_funct_2(C_260, A_262, B_261) | ~v1_funct_1(C_260))), inference(cnfTransformation, [status(thm)], [f_173])).
% 8.79/3.21  tff(c_44, plain, (![C_23, A_21, B_22]: (v4_relat_1(C_23, A_21) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 8.79/3.21  tff(c_2358, plain, (![C_371, B_372, A_373]: (v4_relat_1(k2_funct_1(C_371), B_372) | k2_relset_1(A_373, B_372, C_371)!=B_372 | ~v2_funct_1(C_371) | ~m1_subset_1(C_371, k1_zfmisc_1(k2_zfmisc_1(A_373, B_372))) | ~v1_funct_2(C_371, A_373, B_372) | ~v1_funct_1(C_371))), inference(resolution, [status(thm)], [c_1336, c_44])).
% 8.79/3.21  tff(c_2376, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_699, c_2358])).
% 8.79/3.21  tff(c_2388, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_701, c_76, c_698, c_2376])).
% 8.79/3.21  tff(c_60, plain, (![B_43, A_42]: (k1_relat_1(B_43)=A_42 | ~v1_partfun1(B_43, A_42) | ~v4_relat_1(B_43, A_42) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_157])).
% 8.79/3.21  tff(c_2392, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2388, c_60])).
% 8.79/3.21  tff(c_2395, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1495, c_2392])).
% 8.79/3.21  tff(c_2396, plain, (~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_2395])).
% 8.79/3.21  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.79/3.21  tff(c_1125, plain, (![C_222, A_223, B_224]: (v1_funct_1(k2_funct_1(C_222)) | k2_relset_1(A_223, B_224, C_222)!=B_224 | ~v2_funct_1(C_222) | ~m1_subset_1(C_222, k1_zfmisc_1(k2_zfmisc_1(A_223, B_224))) | ~v1_funct_2(C_222, A_223, B_224) | ~v1_funct_1(C_222))), inference(cnfTransformation, [status(thm)], [f_173])).
% 8.79/3.21  tff(c_1132, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_699, c_1125])).
% 8.79/3.21  tff(c_1140, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_701, c_76, c_698, c_1132])).
% 8.79/3.21  tff(c_26, plain, (![A_13]: (v2_funct_1(k2_funct_1(A_13)) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.79/3.21  tff(c_40, plain, (![A_20]: (k2_funct_1(k2_funct_1(A_20))=A_20 | ~v2_funct_1(A_20) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_113])).
% 8.79/3.21  tff(c_2023, plain, (![A_343, A_344]: (k10_relat_1(k2_funct_1(A_343), A_344)=k9_relat_1(A_343, A_344) | ~v2_funct_1(k2_funct_1(A_343)) | ~v1_funct_1(k2_funct_1(A_343)) | ~v1_relat_1(k2_funct_1(A_343)) | ~v2_funct_1(A_343) | ~v1_funct_1(A_343) | ~v1_relat_1(A_343))), inference(superposition, [status(thm), theory('equality')], [c_40, c_805])).
% 8.79/3.21  tff(c_2100, plain, (![A_360, A_361]: (k10_relat_1(k2_funct_1(A_360), A_361)=k9_relat_1(A_360, A_361) | ~v1_funct_1(k2_funct_1(A_360)) | ~v1_relat_1(k2_funct_1(A_360)) | ~v2_funct_1(A_360) | ~v1_funct_1(A_360) | ~v1_relat_1(A_360))), inference(resolution, [status(thm)], [c_26, c_2023])).
% 8.79/3.21  tff(c_2102, plain, (![A_361]: (k10_relat_1(k2_funct_1('#skF_3'), A_361)=k9_relat_1('#skF_3', A_361) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_1495, c_2100])).
% 8.79/3.21  tff(c_2154, plain, (![A_363]: (k10_relat_1(k2_funct_1('#skF_3'), A_363)=k9_relat_1('#skF_3', A_363))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_84, c_76, c_1140, c_2102])).
% 8.79/3.21  tff(c_812, plain, (![B_156]: (k10_relat_1(B_156, k1_relat_1(k2_funct_1(B_156)))=k2_relat_1(k2_funct_1(B_156)) | ~v1_relat_1(k2_funct_1(B_156)) | ~v2_funct_1(B_156) | ~v1_funct_1(B_156) | ~v1_relat_1(B_156))), inference(superposition, [status(thm), theory('equality')], [c_805, c_16])).
% 8.79/3.21  tff(c_2161, plain, (k9_relat_1('#skF_3', k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))=k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2154, c_812])).
% 8.79/3.21  tff(c_2171, plain, (k9_relat_1('#skF_3', k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))=k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1495, c_1140, c_2161])).
% 8.79/3.21  tff(c_2219, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_2171])).
% 8.79/3.21  tff(c_2222, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_2219])).
% 8.79/3.21  tff(c_2226, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_182, c_84, c_76, c_2222])).
% 8.79/3.21  tff(c_2228, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_2171])).
% 8.79/3.21  tff(c_20, plain, (![A_11]: (k2_relat_1(k6_relat_1(A_11))=A_11)), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.79/3.21  tff(c_36, plain, (![A_19]: (k5_relat_1(k2_funct_1(A_19), A_19)=k6_relat_1(k2_relat_1(A_19)) | ~v2_funct_1(A_19) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_105])).
% 8.79/3.21  tff(c_858, plain, (![A_164]: (k5_relat_1(A_164, k2_funct_1(A_164))=k6_relat_1(k1_relat_1(A_164)) | ~v2_funct_1(A_164) | ~v1_funct_1(A_164) | ~v1_relat_1(A_164))), inference(cnfTransformation, [status(thm)], [f_105])).
% 8.79/3.21  tff(c_2111, plain, (![A_362]: (k6_relat_1(k1_relat_1(k2_funct_1(A_362)))=k5_relat_1(k2_funct_1(A_362), A_362) | ~v2_funct_1(k2_funct_1(A_362)) | ~v1_funct_1(k2_funct_1(A_362)) | ~v1_relat_1(k2_funct_1(A_362)) | ~v2_funct_1(A_362) | ~v1_funct_1(A_362) | ~v1_relat_1(A_362))), inference(superposition, [status(thm), theory('equality')], [c_40, c_858])).
% 8.79/3.21  tff(c_2987, plain, (![A_444]: (k2_relat_1(k5_relat_1(k2_funct_1(A_444), A_444))=k1_relat_1(k2_funct_1(A_444)) | ~v2_funct_1(k2_funct_1(A_444)) | ~v1_funct_1(k2_funct_1(A_444)) | ~v1_relat_1(k2_funct_1(A_444)) | ~v2_funct_1(A_444) | ~v1_funct_1(A_444) | ~v1_relat_1(A_444))), inference(superposition, [status(thm), theory('equality')], [c_2111, c_20])).
% 8.79/3.21  tff(c_3011, plain, (![A_19]: (k2_relat_1(k6_relat_1(k2_relat_1(A_19)))=k1_relat_1(k2_funct_1(A_19)) | ~v2_funct_1(k2_funct_1(A_19)) | ~v1_funct_1(k2_funct_1(A_19)) | ~v1_relat_1(k2_funct_1(A_19)) | ~v2_funct_1(A_19) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19) | ~v2_funct_1(A_19) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(superposition, [status(thm), theory('equality')], [c_36, c_2987])).
% 8.79/3.21  tff(c_3592, plain, (![A_496]: (k1_relat_1(k2_funct_1(A_496))=k2_relat_1(A_496) | ~v2_funct_1(k2_funct_1(A_496)) | ~v1_funct_1(k2_funct_1(A_496)) | ~v1_relat_1(k2_funct_1(A_496)) | ~v2_funct_1(A_496) | ~v1_funct_1(A_496) | ~v1_relat_1(A_496) | ~v2_funct_1(A_496) | ~v1_funct_1(A_496) | ~v1_relat_1(A_496))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_3011])).
% 8.79/3.21  tff(c_3595, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2228, c_3592])).
% 8.79/3.21  tff(c_3604, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_182, c_84, c_76, c_1495, c_1140, c_3595])).
% 8.79/3.21  tff(c_34, plain, (![A_16, B_18]: (r1_tarski(k1_relat_1(A_16), k2_relat_1(B_18)) | ~v2_funct_1(A_16) | k2_relat_1(k5_relat_1(B_18, A_16))!=k2_relat_1(A_16) | ~v1_funct_1(B_18) | ~v1_relat_1(B_18) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.79/3.21  tff(c_1494, plain, (r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1482])).
% 8.79/3.21  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.79/3.21  tff(c_1519, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_3'), k2_relat_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_1494, c_2])).
% 8.79/3.21  tff(c_1531, plain, (~r1_tarski(k1_relat_1('#skF_3'), k2_relat_1(k2_funct_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_1519])).
% 8.79/3.21  tff(c_1537, plain, (~v2_funct_1('#skF_3') | k2_relat_1(k5_relat_1(k2_funct_1('#skF_3'), '#skF_3'))!=k2_relat_1('#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_1531])).
% 8.79/3.21  tff(c_1540, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_3'), '#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_182, c_84, c_1495, c_1140, c_76, c_1537])).
% 8.79/3.21  tff(c_1543, plain, (k2_relat_1(k6_relat_1(k2_relat_1('#skF_3')))!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_36, c_1540])).
% 8.79/3.21  tff(c_1546, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_182, c_84, c_76, c_20, c_1543])).
% 8.79/3.21  tff(c_1547, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_1519])).
% 8.79/3.21  tff(c_2227, plain, (~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | k9_relat_1('#skF_3', k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))=k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_2171])).
% 8.79/3.21  tff(c_2229, plain, (~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_2227])).
% 8.79/3.21  tff(c_2232, plain, (~v1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_40, c_2229])).
% 8.79/3.21  tff(c_2238, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_182, c_84, c_76, c_182, c_2232])).
% 8.79/3.21  tff(c_2240, plain, (v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_2227])).
% 8.79/3.21  tff(c_18, plain, (![A_11]: (k1_relat_1(k6_relat_1(A_11))=A_11)), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.79/3.21  tff(c_1555, plain, (![A_16]: (r1_tarski(k1_relat_1(A_16), k1_relat_1('#skF_3')) | ~v2_funct_1(A_16) | k2_relat_1(k5_relat_1(k2_funct_1('#skF_3'), A_16))!=k2_relat_1(A_16) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(superposition, [status(thm), theory('equality')], [c_1547, c_34])).
% 8.79/3.21  tff(c_1600, plain, (![A_276]: (r1_tarski(k1_relat_1(A_276), k1_relat_1('#skF_3')) | ~v2_funct_1(A_276) | k2_relat_1(k5_relat_1(k2_funct_1('#skF_3'), A_276))!=k2_relat_1(A_276) | ~v1_funct_1(A_276) | ~v1_relat_1(A_276))), inference(demodulation, [status(thm), theory('equality')], [c_1495, c_1140, c_1555])).
% 8.79/3.21  tff(c_1608, plain, (![A_11]: (r1_tarski(A_11, k1_relat_1('#skF_3')) | ~v2_funct_1(k6_relat_1(A_11)) | k2_relat_1(k5_relat_1(k2_funct_1('#skF_3'), k6_relat_1(A_11)))!=k2_relat_1(k6_relat_1(A_11)) | ~v1_funct_1(k6_relat_1(A_11)) | ~v1_relat_1(k6_relat_1(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1600])).
% 8.79/3.21  tff(c_1611, plain, (![A_11]: (r1_tarski(A_11, k1_relat_1('#skF_3')) | ~v2_funct_1(k6_relat_1(A_11)) | k2_relat_1(k5_relat_1(k2_funct_1('#skF_3'), k6_relat_1(A_11)))!=A_11 | ~v1_funct_1(k6_relat_1(A_11)) | ~v1_relat_1(k6_relat_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1608])).
% 8.79/3.21  tff(c_2397, plain, (![A_374]: (r1_tarski(k1_relat_1(k2_funct_1(A_374)), k1_relat_1('#skF_3')) | ~v2_funct_1(k6_relat_1(k1_relat_1(k2_funct_1(A_374)))) | k2_relat_1(k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1(k2_funct_1(A_374), A_374)))!=k1_relat_1(k2_funct_1(A_374)) | ~v1_funct_1(k6_relat_1(k1_relat_1(k2_funct_1(A_374)))) | ~v1_relat_1(k6_relat_1(k1_relat_1(k2_funct_1(A_374)))) | ~v2_funct_1(k2_funct_1(A_374)) | ~v1_funct_1(k2_funct_1(A_374)) | ~v1_relat_1(k2_funct_1(A_374)) | ~v2_funct_1(A_374) | ~v1_funct_1(A_374) | ~v1_relat_1(A_374))), inference(superposition, [status(thm), theory('equality')], [c_2111, c_1611])).
% 8.79/3.21  tff(c_2791, plain, (![A_434]: (r1_tarski(k1_relat_1(k2_funct_1(A_434)), k1_relat_1('#skF_3')) | ~v2_funct_1(k6_relat_1(k1_relat_1(k2_funct_1(A_434)))) | k2_relat_1(k5_relat_1(k2_funct_1('#skF_3'), k6_relat_1(k2_relat_1(A_434))))!=k1_relat_1(k2_funct_1(A_434)) | ~v1_funct_1(k6_relat_1(k1_relat_1(k2_funct_1(A_434)))) | ~v1_relat_1(k6_relat_1(k1_relat_1(k2_funct_1(A_434)))) | ~v2_funct_1(k2_funct_1(A_434)) | ~v1_funct_1(k2_funct_1(A_434)) | ~v1_relat_1(k2_funct_1(A_434)) | ~v2_funct_1(A_434) | ~v1_funct_1(A_434) | ~v1_relat_1(A_434) | ~v2_funct_1(A_434) | ~v1_funct_1(A_434) | ~v1_relat_1(A_434))), inference(superposition, [status(thm), theory('equality')], [c_36, c_2397])).
% 8.79/3.21  tff(c_2797, plain, (r1_tarski(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))), k1_relat_1('#skF_3')) | ~v2_funct_1(k6_relat_1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))) | k2_relat_1(k5_relat_1(k2_funct_1('#skF_3'), k6_relat_1(k1_relat_1('#skF_3'))))!=k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k6_relat_1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))) | ~v1_relat_1(k6_relat_1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1547, c_2791])).
% 8.79/3.21  tff(c_2804, plain, (r1_tarski(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))), k1_relat_1('#skF_3')) | ~v2_funct_1(k6_relat_1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))) | k2_relat_1(k5_relat_1(k2_funct_1('#skF_3'), k6_relat_1(k1_relat_1('#skF_3'))))!=k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k6_relat_1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))) | ~v1_relat_1(k6_relat_1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1495, c_1140, c_2228, c_1495, c_1140, c_2228, c_2240, c_2797])).
% 8.79/3.21  tff(c_3019, plain, (~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_2804])).
% 8.79/3.21  tff(c_3022, plain, (~v1_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_40, c_3019])).
% 8.79/3.21  tff(c_3028, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_182, c_84, c_76, c_84, c_3022])).
% 8.79/3.21  tff(c_3030, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_2804])).
% 8.79/3.21  tff(c_2239, plain, (k9_relat_1('#skF_3', k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))=k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_2227])).
% 8.79/3.21  tff(c_2282, plain, (k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))=k9_relat_1('#skF_3', k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_40, c_2239])).
% 8.79/3.21  tff(c_2286, plain, (k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))=k9_relat_1('#skF_3', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_84, c_76, c_2282])).
% 8.79/3.21  tff(c_2295, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_40, c_2286])).
% 8.79/3.21  tff(c_2301, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_182, c_84, c_76, c_2295])).
% 8.79/3.21  tff(c_2315, plain, (k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2301, c_2286])).
% 8.79/3.21  tff(c_2335, plain, (![A_16]: (r1_tarski(k1_relat_1(A_16), k2_relat_1('#skF_3')) | ~v2_funct_1(A_16) | k2_relat_1(k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), A_16))!=k2_relat_1(A_16) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(superposition, [status(thm), theory('equality')], [c_2315, c_34])).
% 8.79/3.21  tff(c_2342, plain, (![A_16]: (r1_tarski(k1_relat_1(A_16), k2_relat_1('#skF_3')) | ~v2_funct_1(A_16) | k2_relat_1(k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), A_16))!=k2_relat_1(A_16) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(demodulation, [status(thm), theory('equality')], [c_2240, c_2335])).
% 8.79/3.21  tff(c_3111, plain, (![A_447]: (r1_tarski(k1_relat_1(A_447), k2_relat_1('#skF_3')) | ~v2_funct_1(A_447) | k2_relat_1(k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), A_447))!=k2_relat_1(A_447) | ~v1_funct_1(A_447) | ~v1_relat_1(A_447))), inference(demodulation, [status(thm), theory('equality')], [c_3030, c_2342])).
% 8.79/3.21  tff(c_3135, plain, (r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), k2_relat_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relat_1(k6_relat_1(k2_relat_1(k2_funct_1('#skF_3'))))!=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_3111])).
% 8.79/3.21  tff(c_3151, plain, (r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1495, c_1140, c_2228, c_1495, c_1140, c_20, c_1547, c_1547, c_2228, c_3135])).
% 8.79/3.21  tff(c_3217, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~r1_tarski(k2_relat_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_3151, c_2])).
% 8.79/3.21  tff(c_3225, plain, (~r1_tarski(k2_relat_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_3217])).
% 8.79/3.21  tff(c_3606, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3604, c_3225])).
% 8.79/3.21  tff(c_3611, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_3606])).
% 8.79/3.21  tff(c_3612, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_3217])).
% 8.79/3.21  tff(c_58, plain, (![B_43]: (v1_partfun1(B_43, k1_relat_1(B_43)) | ~v4_relat_1(B_43, k1_relat_1(B_43)) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_157])).
% 8.79/3.21  tff(c_3635, plain, (v1_partfun1(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3'))) | ~v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3612, c_58])).
% 8.79/3.21  tff(c_3652, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1495, c_2388, c_3612, c_3635])).
% 8.79/3.21  tff(c_3654, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2396, c_3652])).
% 8.79/3.21  tff(c_3655, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_2395])).
% 8.79/3.21  tff(c_48, plain, (![A_28, B_29, C_30]: (k1_relset_1(A_28, B_29, C_30)=k1_relat_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.79/3.21  tff(c_5073, plain, (![B_625, A_626, C_627]: (k1_relset_1(B_625, A_626, k2_funct_1(C_627))=k1_relat_1(k2_funct_1(C_627)) | k2_relset_1(A_626, B_625, C_627)!=B_625 | ~v2_funct_1(C_627) | ~m1_subset_1(C_627, k1_zfmisc_1(k2_zfmisc_1(A_626, B_625))) | ~v1_funct_2(C_627, A_626, B_625) | ~v1_funct_1(C_627))), inference(resolution, [status(thm)], [c_1336, c_48])).
% 8.79/3.21  tff(c_5095, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_699, c_5073])).
% 8.79/3.21  tff(c_5108, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_701, c_76, c_698, c_3655, c_5095])).
% 8.79/3.21  tff(c_5110, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1324, c_5108])).
% 8.79/3.21  tff(c_5111, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_205])).
% 8.79/3.21  tff(c_5707, plain, (k2_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5611, c_5611, c_5611, c_5111])).
% 8.79/3.21  tff(c_5765, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5739, c_5739, c_5707])).
% 8.79/3.21  tff(c_6320, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6253, c_5765])).
% 8.79/3.21  tff(c_5744, plain, (![B_718, A_719]: (k9_relat_1(k2_funct_1(B_718), A_719)=k10_relat_1(B_718, A_719) | ~v2_funct_1(B_718) | ~v1_funct_1(B_718) | ~v1_relat_1(B_718))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.79/3.21  tff(c_6426, plain, (![B_825]: (k10_relat_1(B_825, k1_relat_1(k2_funct_1(B_825)))=k2_relat_1(k2_funct_1(B_825)) | ~v2_funct_1(B_825) | ~v1_funct_1(B_825) | ~v1_relat_1(B_825) | ~v1_relat_1(k2_funct_1(B_825)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_5744])).
% 8.79/3.21  tff(c_5900, plain, (![A_727, B_728, C_729, D_730]: (k8_relset_1(A_727, B_728, C_729, D_730)=k10_relat_1(C_729, D_730) | ~m1_subset_1(C_729, k1_zfmisc_1(k2_zfmisc_1(A_727, B_728))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 8.79/3.21  tff(c_5906, plain, (![D_730]: (k8_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', D_730)=k10_relat_1('#skF_3', D_730))), inference(resolution, [status(thm)], [c_5767, c_5900])).
% 8.79/3.21  tff(c_5936, plain, (![A_739, B_740, C_741, D_742]: (m1_subset_1(k8_relset_1(A_739, B_740, C_741, D_742), k1_zfmisc_1(A_739)) | ~m1_subset_1(C_741, k1_zfmisc_1(k2_zfmisc_1(A_739, B_740))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 8.79/3.21  tff(c_5967, plain, (![D_730]: (m1_subset_1(k10_relat_1('#skF_3', D_730), k1_zfmisc_1(k1_relat_1('#skF_3'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))))), inference(superposition, [status(thm), theory('equality')], [c_5906, c_5936])).
% 8.79/3.21  tff(c_5976, plain, (![D_730]: (m1_subset_1(k10_relat_1('#skF_3', D_730), k1_zfmisc_1(k1_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_5767, c_5967])).
% 8.79/3.21  tff(c_6473, plain, (m1_subset_1(k2_relat_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k1_relat_1('#skF_3'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_6426, c_5976])).
% 8.79/3.21  tff(c_6502, plain, (m1_subset_1(k2_relat_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k1_relat_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_84, c_76, c_6473])).
% 8.79/3.21  tff(c_6514, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_6502])).
% 8.79/3.21  tff(c_6517, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_6514])).
% 8.79/3.21  tff(c_6521, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_182, c_84, c_6517])).
% 8.79/3.21  tff(c_6523, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_6502])).
% 8.79/3.21  tff(c_6142, plain, (![C_780, A_781, B_782]: (v1_funct_1(k2_funct_1(C_780)) | k2_relset_1(A_781, B_782, C_780)!=B_782 | ~v2_funct_1(C_780) | ~m1_subset_1(C_780, k1_zfmisc_1(k2_zfmisc_1(A_781, B_782))) | ~v1_funct_2(C_780, A_781, B_782) | ~v1_funct_1(C_780))), inference(cnfTransformation, [status(thm)], [f_173])).
% 8.79/3.21  tff(c_6149, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_5767, c_6142])).
% 8.79/3.21  tff(c_6157, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_5769, c_76, c_5764, c_6149])).
% 8.79/3.21  tff(c_5977, plain, (![D_743]: (m1_subset_1(k10_relat_1('#skF_3', D_743), k1_zfmisc_1(k1_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_5767, c_5967])).
% 8.79/3.21  tff(c_5985, plain, (![D_743]: (r1_tarski(k10_relat_1('#skF_3', D_743), k1_relat_1('#skF_3')))), inference(resolution, [status(thm)], [c_5977, c_8])).
% 8.79/3.21  tff(c_6469, plain, (r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_6426, c_5985])).
% 8.79/3.21  tff(c_6500, plain, (r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_84, c_76, c_6469])).
% 8.79/3.21  tff(c_6504, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_6500])).
% 8.79/3.21  tff(c_6507, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_6504])).
% 8.79/3.21  tff(c_6511, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_182, c_84, c_6507])).
% 8.79/3.21  tff(c_6512, plain, (r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_6500])).
% 8.79/3.21  tff(c_6531, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_3'), k2_relat_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_6512, c_2])).
% 8.79/3.21  tff(c_6558, plain, (~r1_tarski(k1_relat_1('#skF_3'), k2_relat_1(k2_funct_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_6531])).
% 8.79/3.21  tff(c_6561, plain, (~v2_funct_1('#skF_3') | k2_relat_1(k5_relat_1(k2_funct_1('#skF_3'), '#skF_3'))!=k2_relat_1('#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_6558])).
% 8.79/3.21  tff(c_6564, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_3'), '#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_182, c_84, c_6523, c_6157, c_76, c_6561])).
% 8.79/3.21  tff(c_6567, plain, (k2_relat_1(k6_relat_1(k2_relat_1('#skF_3')))!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_36, c_6564])).
% 8.79/3.21  tff(c_6570, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_182, c_84, c_76, c_20, c_6567])).
% 8.79/3.21  tff(c_6571, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_6531])).
% 8.79/3.21  tff(c_6371, plain, (![C_822, B_823, A_824]: (m1_subset_1(k2_funct_1(C_822), k1_zfmisc_1(k2_zfmisc_1(B_823, A_824))) | k2_relset_1(A_824, B_823, C_822)!=B_823 | ~v2_funct_1(C_822) | ~m1_subset_1(C_822, k1_zfmisc_1(k2_zfmisc_1(A_824, B_823))) | ~v1_funct_2(C_822, A_824, B_823) | ~v1_funct_1(C_822))), inference(cnfTransformation, [status(thm)], [f_173])).
% 8.79/3.21  tff(c_50, plain, (![A_31, B_32, C_33]: (k2_relset_1(A_31, B_32, C_33)=k2_relat_1(C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_131])).
% 8.79/3.21  tff(c_9017, plain, (![B_1065, A_1066, C_1067]: (k2_relset_1(B_1065, A_1066, k2_funct_1(C_1067))=k2_relat_1(k2_funct_1(C_1067)) | k2_relset_1(A_1066, B_1065, C_1067)!=B_1065 | ~v2_funct_1(C_1067) | ~m1_subset_1(C_1067, k1_zfmisc_1(k2_zfmisc_1(A_1066, B_1065))) | ~v1_funct_2(C_1067, A_1066, B_1065) | ~v1_funct_1(C_1067))), inference(resolution, [status(thm)], [c_6371, c_50])).
% 8.79/3.21  tff(c_9039, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_5767, c_9017])).
% 8.79/3.21  tff(c_9052, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_5769, c_76, c_5764, c_6571, c_9039])).
% 8.79/3.21  tff(c_9054, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6320, c_9052])).
% 8.79/3.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.79/3.21  
% 8.79/3.21  Inference rules
% 8.79/3.21  ----------------------
% 8.79/3.21  #Ref     : 0
% 8.79/3.21  #Sup     : 1961
% 8.79/3.21  #Fact    : 0
% 8.79/3.21  #Define  : 0
% 8.79/3.21  #Split   : 41
% 8.79/3.21  #Chain   : 0
% 8.79/3.21  #Close   : 0
% 8.79/3.21  
% 8.79/3.21  Ordering : KBO
% 8.79/3.21  
% 8.79/3.21  Simplification rules
% 8.79/3.21  ----------------------
% 8.79/3.21  #Subsume      : 168
% 8.79/3.21  #Demod        : 1901
% 8.79/3.21  #Tautology    : 582
% 8.79/3.21  #SimpNegUnit  : 16
% 8.79/3.21  #BackRed      : 83
% 8.79/3.21  
% 8.79/3.21  #Partial instantiations: 0
% 8.79/3.21  #Strategies tried      : 1
% 8.79/3.21  
% 8.79/3.21  Timing (in seconds)
% 8.79/3.21  ----------------------
% 8.79/3.21  Preprocessing        : 0.38
% 8.79/3.21  Parsing              : 0.21
% 8.79/3.21  CNF conversion       : 0.02
% 8.79/3.21  Main loop            : 2.01
% 8.79/3.21  Inferencing          : 0.65
% 8.79/3.21  Reduction            : 0.73
% 8.79/3.21  Demodulation         : 0.56
% 8.79/3.21  BG Simplification    : 0.09
% 8.79/3.21  Subsumption          : 0.39
% 8.79/3.21  Abstraction          : 0.12
% 8.79/3.21  MUC search           : 0.00
% 8.79/3.22  Cooper               : 0.00
% 8.79/3.22  Total                : 2.48
% 8.79/3.22  Index Insertion      : 0.00
% 8.79/3.22  Index Deletion       : 0.00
% 8.79/3.22  Index Matching       : 0.00
% 8.79/3.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
