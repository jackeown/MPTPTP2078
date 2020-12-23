%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:23 EST 2020

% Result     : Theorem 5.60s
% Output     : CNFRefutation 5.85s
% Verified   : 
% Statistics : Number of formulae       :  231 (6330 expanded)
%              Number of leaves         :   51 (2242 expanded)
%              Depth                    :   24
%              Number of atoms          :  433 (18759 expanded)
%              Number of equality atoms :  114 (5528 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_181,negated_conjecture,(
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

tff(f_137,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_111,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_145,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

tff(f_50,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_133,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_125,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_157,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_76,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_87,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v2_funct_1(A)
            & r1_tarski(B,k1_relat_1(A)) )
         => k9_relat_1(k2_funct_1(A),k9_relat_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t177_funct_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_97,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_70,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_72,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_76,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_80,plain,(
    ! [A_50] :
      ( u1_struct_0(A_50) = k2_struct_0(A_50)
      | ~ l1_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_88,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_76,c_80])).

tff(c_87,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_80])).

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_123,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_87,c_66])).

tff(c_2709,plain,(
    ! [A_283,B_284,C_285] :
      ( k2_relset_1(A_283,B_284,C_285) = k2_relat_1(C_285)
      | ~ m1_subset_1(C_285,k1_zfmisc_1(k2_zfmisc_1(A_283,B_284))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2717,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_123,c_2709])).

tff(c_64,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_118,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_87,c_64])).

tff(c_2719,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2717,c_118])).

tff(c_56,plain,(
    ! [A_39] :
      ( ~ v1_xboole_0(k2_struct_0(A_39))
      | ~ l1_struct_0(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_2737,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2719,c_56])).

tff(c_2741,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2737])).

tff(c_2742,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_2741])).

tff(c_18,plain,(
    ! [A_10,B_11] : v1_relat_1(k2_zfmisc_1(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_12,plain,(
    ! [B_7,A_5] :
      ( v1_relat_1(B_7)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_5))
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_126,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_123,c_12])).

tff(c_132,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_126])).

tff(c_177,plain,(
    ! [C_68,A_69,B_70] :
      ( v4_relat_1(C_68,A_69)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_185,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_123,c_177])).

tff(c_2590,plain,(
    ! [B_268,A_269] :
      ( k1_relat_1(B_268) = A_269
      | ~ v1_partfun1(B_268,A_269)
      | ~ v4_relat_1(B_268,A_269)
      | ~ v1_relat_1(B_268) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_2599,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_185,c_2590])).

tff(c_2607,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_2599])).

tff(c_2609,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_2607])).

tff(c_68,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_93,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_68])).

tff(c_94,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_93])).

tff(c_2732,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2719,c_94])).

tff(c_2731,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2719,c_123])).

tff(c_46,plain,(
    ! [C_35,A_32,B_33] :
      ( v1_partfun1(C_35,A_32)
      | ~ v1_funct_2(C_35,A_32,B_33)
      | ~ v1_funct_1(C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33)))
      | v1_xboole_0(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_2779,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2731,c_46])).

tff(c_2800,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2732,c_2779])).

tff(c_2802,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2742,c_2609,c_2800])).

tff(c_2803,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_2607])).

tff(c_2812,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2803,c_123])).

tff(c_3018,plain,(
    ! [A_305,B_306,C_307] :
      ( k2_relset_1(A_305,B_306,C_307) = k2_relat_1(C_307)
      | ~ m1_subset_1(C_307,k1_zfmisc_1(k2_zfmisc_1(A_305,B_306))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_3026,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2812,c_3018])).

tff(c_2813,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2803,c_118])).

tff(c_3038,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3026,c_2813])).

tff(c_2814,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2803,c_94])).

tff(c_3046,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3038,c_2814])).

tff(c_3043,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3038,c_3026])).

tff(c_62,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_3047,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3038,c_2812])).

tff(c_3382,plain,(
    ! [A_335,B_336,C_337] :
      ( k2_tops_2(A_335,B_336,C_337) = k2_funct_1(C_337)
      | ~ v2_funct_1(C_337)
      | k2_relset_1(A_335,B_336,C_337) != B_336
      | ~ m1_subset_1(C_337,k1_zfmisc_1(k2_zfmisc_1(A_335,B_336)))
      | ~ v1_funct_2(C_337,A_335,B_336)
      | ~ v1_funct_1(C_337) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_3385,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3047,c_3382])).

tff(c_3392,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_3046,c_3043,c_62,c_3385])).

tff(c_513,plain,(
    ! [A_128,B_129,C_130] :
      ( k2_relset_1(A_128,B_129,C_130) = k2_relat_1(C_130)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_521,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_123,c_513])).

tff(c_523,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_521,c_118])).

tff(c_540,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_523,c_56])).

tff(c_544,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_540])).

tff(c_545,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_544])).

tff(c_361,plain,(
    ! [B_103,A_104] :
      ( k1_relat_1(B_103) = A_104
      | ~ v1_partfun1(B_103,A_104)
      | ~ v4_relat_1(B_103,A_104)
      | ~ v1_relat_1(B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_370,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_185,c_361])).

tff(c_378,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_370])).

tff(c_379,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_378])).

tff(c_535,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_523,c_94])).

tff(c_534,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_523,c_123])).

tff(c_644,plain,(
    ! [C_133,A_134,B_135] :
      ( v1_partfun1(C_133,A_134)
      | ~ v1_funct_2(C_133,A_134,B_135)
      | ~ v1_funct_1(C_133)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135)))
      | v1_xboole_0(B_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_647,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_534,c_644])).

tff(c_654,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_535,c_647])).

tff(c_656,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_545,c_379,c_654])).

tff(c_657,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_378])).

tff(c_666,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_657,c_123])).

tff(c_920,plain,(
    ! [A_159,B_160,C_161] :
      ( k2_relset_1(A_159,B_160,C_161) = k2_relat_1(C_161)
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(A_159,B_160))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_928,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_666,c_920])).

tff(c_667,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_657,c_118])).

tff(c_930,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_928,c_667])).

tff(c_668,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_657,c_94])).

tff(c_941,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_930,c_668])).

tff(c_935,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_930,c_928])).

tff(c_940,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_930,c_666])).

tff(c_1261,plain,(
    ! [A_183,B_184,C_185] :
      ( k2_tops_2(A_183,B_184,C_185) = k2_funct_1(C_185)
      | ~ v2_funct_1(C_185)
      | k2_relset_1(A_183,B_184,C_185) != B_184
      | ~ m1_subset_1(C_185,k1_zfmisc_1(k2_zfmisc_1(A_183,B_184)))
      | ~ v1_funct_2(C_185,A_183,B_184)
      | ~ v1_funct_1(C_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_1264,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_940,c_1261])).

tff(c_1271,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_941,c_935,c_62,c_1264])).

tff(c_60,plain,
    ( k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_187,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_88,c_87,c_87,c_88,c_88,c_87,c_87,c_60])).

tff(c_188,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_187])).

tff(c_661,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_657,c_657,c_188])).

tff(c_937,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_930,c_930,c_930,c_661])).

tff(c_1273,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1271,c_937])).

tff(c_30,plain,(
    ! [A_18] :
      ( v1_relat_1(k2_funct_1(A_18))
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_211,plain,(
    ! [B_77,A_78] :
      ( k7_relat_1(B_77,A_78) = B_77
      | ~ v4_relat_1(B_77,A_78)
      | ~ v1_relat_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_220,plain,
    ( k7_relat_1('#skF_3',k2_struct_0('#skF_1')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_185,c_211])).

tff(c_227,plain,(
    k7_relat_1('#skF_3',k2_struct_0('#skF_1')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_220])).

tff(c_663,plain,(
    k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_657,c_227])).

tff(c_22,plain,(
    ! [B_14,A_13] :
      ( k2_relat_1(k7_relat_1(B_14,A_13)) = k9_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_709,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_663,c_22])).

tff(c_719,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_709])).

tff(c_1129,plain,(
    ! [A_175,B_176] :
      ( k9_relat_1(k2_funct_1(A_175),k9_relat_1(A_175,B_176)) = B_176
      | ~ r1_tarski(B_176,k1_relat_1(A_175))
      | ~ v2_funct_1(A_175)
      | ~ v1_funct_1(A_175)
      | ~ v1_relat_1(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1144,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_719,c_1129])).

tff(c_1154,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_70,c_62,c_6,c_1144])).

tff(c_26,plain,(
    ! [A_17] :
      ( r1_tarski(A_17,k2_zfmisc_1(k1_relat_1(A_17),k2_relat_1(A_17)))
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_294,plain,(
    ! [C_86,B_87,A_88] :
      ( v5_relat_1(C_86,B_87)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_88,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_304,plain,(
    ! [A_89,B_90,A_91] :
      ( v5_relat_1(A_89,B_90)
      | ~ r1_tarski(A_89,k2_zfmisc_1(A_91,B_90)) ) ),
    inference(resolution,[status(thm)],[c_10,c_294])).

tff(c_330,plain,(
    ! [A_95] :
      ( v5_relat_1(A_95,k2_relat_1(A_95))
      | ~ v1_relat_1(A_95) ) ),
    inference(resolution,[status(thm)],[c_26,c_304])).

tff(c_1196,plain,(
    ! [B_178,A_179] :
      ( v5_relat_1(k7_relat_1(B_178,A_179),k9_relat_1(B_178,A_179))
      | ~ v1_relat_1(k7_relat_1(B_178,A_179))
      | ~ v1_relat_1(B_178) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_330])).

tff(c_1202,plain,
    ( v5_relat_1(k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')),k1_relat_1('#skF_3'))
    | ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1154,c_1196])).

tff(c_1296,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1202])).

tff(c_1299,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_1296])).

tff(c_1303,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_70,c_1299])).

tff(c_1305,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1202])).

tff(c_36,plain,(
    ! [A_22] :
      ( k1_relat_1(k2_funct_1(A_22)) = k2_relat_1(A_22)
      | ~ v2_funct_1(A_22)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_726,plain,(
    ! [A_136] :
      ( k1_relat_1(k2_funct_1(A_136)) = k2_relat_1(A_136)
      | ~ v2_funct_1(A_136)
      | ~ v1_funct_1(A_136)
      | ~ v1_relat_1(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_20,plain,(
    ! [A_12] :
      ( k9_relat_1(A_12,k1_relat_1(A_12)) = k2_relat_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1957,plain,(
    ! [A_235] :
      ( k9_relat_1(k2_funct_1(A_235),k2_relat_1(A_235)) = k2_relat_1(k2_funct_1(A_235))
      | ~ v1_relat_1(k2_funct_1(A_235))
      | ~ v2_funct_1(A_235)
      | ~ v1_funct_1(A_235)
      | ~ v1_relat_1(A_235) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_726,c_20])).

tff(c_1969,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1957,c_1154])).

tff(c_1990,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_70,c_62,c_1305,c_1969])).

tff(c_2024,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1990,c_26])).

tff(c_2050,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1305,c_2024])).

tff(c_186,plain,(
    ! [A_3,A_69,B_70] :
      ( v4_relat_1(A_3,A_69)
      | ~ r1_tarski(A_3,k2_zfmisc_1(A_69,B_70)) ) ),
    inference(resolution,[status(thm)],[c_10,c_177])).

tff(c_2088,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_2050,c_186])).

tff(c_2107,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_2088])).

tff(c_2124,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_70,c_62,c_2107])).

tff(c_28,plain,(
    ! [A_18] :
      ( v1_funct_1(k2_funct_1(A_18))
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_32,plain,(
    ! [A_19,B_21] :
      ( k9_relat_1(k2_funct_1(A_19),k9_relat_1(A_19,B_21)) = B_21
      | ~ r1_tarski(B_21,k1_relat_1(A_19))
      | ~ v2_funct_1(A_19)
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1162,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ r1_tarski(k2_relat_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1154,c_32])).

tff(c_1795,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ r1_tarski(k2_relat_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1305,c_1162])).

tff(c_1796,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1795])).

tff(c_1799,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_1796])).

tff(c_1803,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_70,c_1799])).

tff(c_1804,plain,
    ( ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ r1_tarski(k2_relat_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')))
    | k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1795])).

tff(c_1924,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_1804])).

tff(c_1927,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1924])).

tff(c_1930,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_70,c_62,c_6,c_1927])).

tff(c_1932,plain,(
    r1_tarski(k2_relat_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_1804])).

tff(c_169,plain,(
    ! [B_66,A_67] :
      ( r1_tarski(k1_relat_1(B_66),A_67)
      | ~ v4_relat_1(B_66,A_67)
      | ~ v1_relat_1(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_175,plain,(
    ! [B_66,A_67] :
      ( k1_relat_1(B_66) = A_67
      | ~ r1_tarski(A_67,k1_relat_1(B_66))
      | ~ v4_relat_1(B_66,A_67)
      | ~ v1_relat_1(B_66) ) ),
    inference(resolution,[status(thm)],[c_169,c_2])).

tff(c_1935,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1932,c_175])).

tff(c_1946,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1305,c_1935])).

tff(c_2309,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2124,c_1946])).

tff(c_868,plain,(
    ! [A_152,B_153,C_154] :
      ( k1_relset_1(A_152,B_153,C_154) = k1_relat_1(C_154)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(A_152,B_153))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_882,plain,(
    ! [A_155,B_156,A_157] :
      ( k1_relset_1(A_155,B_156,A_157) = k1_relat_1(A_157)
      | ~ r1_tarski(A_157,k2_zfmisc_1(A_155,B_156)) ) ),
    inference(resolution,[status(thm)],[c_10,c_868])).

tff(c_900,plain,(
    ! [A_17] :
      ( k1_relset_1(k1_relat_1(A_17),k2_relat_1(A_17),A_17) = k1_relat_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(resolution,[status(thm)],[c_26,c_882])).

tff(c_2358,plain,
    ( k1_relset_1(k2_relat_1('#skF_3'),k2_relat_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2309,c_900])).

tff(c_2411,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1305,c_2309,c_1990,c_2358])).

tff(c_2413,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1273,c_2411])).

tff(c_2414,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_187])).

tff(c_2806,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2803,c_2803,c_2803,c_2414])).

tff(c_3338,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3038,c_3038,c_2806])).

tff(c_3395,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3392,c_3338])).

tff(c_2437,plain,(
    ! [B_243,A_244] :
      ( k7_relat_1(B_243,A_244) = B_243
      | ~ v4_relat_1(B_243,A_244)
      | ~ v1_relat_1(B_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2443,plain,
    ( k7_relat_1('#skF_3',k2_struct_0('#skF_1')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_185,c_2437])).

tff(c_2449,plain,(
    k7_relat_1('#skF_3',k2_struct_0('#skF_1')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_2443])).

tff(c_2512,plain,(
    ! [B_257,A_258] :
      ( k2_relat_1(k7_relat_1(B_257,A_258)) = k9_relat_1(B_257,A_258)
      | ~ v1_relat_1(B_257) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2530,plain,
    ( k9_relat_1('#skF_3',k2_struct_0('#skF_1')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2449,c_2512])).

tff(c_2536,plain,(
    k9_relat_1('#skF_3',k2_struct_0('#skF_1')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_2530])).

tff(c_2807,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2803,c_2536])).

tff(c_3256,plain,(
    ! [A_326,B_327] :
      ( k9_relat_1(k2_funct_1(A_326),k9_relat_1(A_326,B_327)) = B_327
      | ~ r1_tarski(B_327,k1_relat_1(A_326))
      | ~ v2_funct_1(A_326)
      | ~ v1_funct_1(A_326)
      | ~ v1_relat_1(A_326) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_3271,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2807,c_3256])).

tff(c_3281,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_70,c_62,c_6,c_3271])).

tff(c_2481,plain,(
    ! [C_249,B_250,A_251] :
      ( v5_relat_1(C_249,B_250)
      | ~ m1_subset_1(C_249,k1_zfmisc_1(k2_zfmisc_1(A_251,B_250))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2491,plain,(
    ! [A_252,B_253,A_254] :
      ( v5_relat_1(A_252,B_253)
      | ~ r1_tarski(A_252,k2_zfmisc_1(A_254,B_253)) ) ),
    inference(resolution,[status(thm)],[c_10,c_2481])).

tff(c_2537,plain,(
    ! [A_259] :
      ( v5_relat_1(A_259,k2_relat_1(A_259))
      | ~ v1_relat_1(A_259) ) ),
    inference(resolution,[status(thm)],[c_26,c_2491])).

tff(c_3339,plain,(
    ! [B_331,A_332] :
      ( v5_relat_1(k7_relat_1(B_331,A_332),k9_relat_1(B_331,A_332))
      | ~ v1_relat_1(k7_relat_1(B_331,A_332))
      | ~ v1_relat_1(B_331) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_2537])).

tff(c_3345,plain,
    ( v5_relat_1(k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')),k1_relat_1('#skF_3'))
    | ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3281,c_3339])).

tff(c_3546,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3345])).

tff(c_3549,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_3546])).

tff(c_3553,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_70,c_3549])).

tff(c_3555,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_3345])).

tff(c_2849,plain,(
    ! [A_289] :
      ( k1_relat_1(k2_funct_1(A_289)) = k2_relat_1(A_289)
      | ~ v2_funct_1(A_289)
      | ~ v1_funct_1(A_289)
      | ~ v1_relat_1(A_289) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_3786,plain,(
    ! [A_377] :
      ( k9_relat_1(k2_funct_1(A_377),k2_relat_1(A_377)) = k2_relat_1(k2_funct_1(A_377))
      | ~ v1_relat_1(k2_funct_1(A_377))
      | ~ v2_funct_1(A_377)
      | ~ v1_funct_1(A_377)
      | ~ v1_relat_1(A_377) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2849,c_20])).

tff(c_3798,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3786,c_3281])).

tff(c_3819,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_70,c_62,c_3555,c_3798])).

tff(c_3856,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3819,c_26])).

tff(c_3884,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3555,c_3856])).

tff(c_3987,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_3884])).

tff(c_4003,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_70,c_62,c_3987])).

tff(c_3027,plain,(
    ! [A_305,B_306,A_3] :
      ( k2_relset_1(A_305,B_306,A_3) = k2_relat_1(A_3)
      | ~ r1_tarski(A_3,k2_zfmisc_1(A_305,B_306)) ) ),
    inference(resolution,[status(thm)],[c_10,c_3018])).

tff(c_4091,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_4003,c_3027])).

tff(c_4110,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3819,c_4091])).

tff(c_4112,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3395,c_4110])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 21:07:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.60/2.05  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.60/2.09  
% 5.60/2.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.60/2.09  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 5.60/2.09  
% 5.60/2.09  %Foreground sorts:
% 5.60/2.09  
% 5.60/2.09  
% 5.60/2.09  %Background operators:
% 5.60/2.09  
% 5.60/2.09  
% 5.60/2.09  %Foreground operators:
% 5.60/2.09  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.60/2.09  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.60/2.09  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.60/2.09  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.60/2.09  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.60/2.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.60/2.09  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.60/2.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.60/2.09  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.60/2.09  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 5.60/2.09  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.60/2.09  tff('#skF_2', type, '#skF_2': $i).
% 5.60/2.09  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.60/2.09  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.60/2.09  tff('#skF_3', type, '#skF_3': $i).
% 5.60/2.09  tff('#skF_1', type, '#skF_1': $i).
% 5.60/2.09  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.60/2.09  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.60/2.09  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.60/2.09  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.60/2.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.60/2.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.60/2.09  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.60/2.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.60/2.09  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.60/2.09  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.60/2.09  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.60/2.09  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.60/2.09  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.60/2.09  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.60/2.09  
% 5.85/2.12  tff(f_181, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_2)).
% 5.85/2.12  tff(f_137, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 5.85/2.12  tff(f_111, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.85/2.12  tff(f_145, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_struct_0)).
% 5.85/2.12  tff(f_50, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.85/2.12  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.85/2.12  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.85/2.12  tff(f_133, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 5.85/2.12  tff(f_125, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 5.85/2.12  tff(f_157, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 5.85/2.12  tff(f_76, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 5.85/2.12  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.85/2.12  tff(f_64, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 5.85/2.12  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 5.85/2.12  tff(f_87, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v2_funct_1(A) & r1_tarski(B, k1_relat_1(A))) => (k9_relat_1(k2_funct_1(A), k9_relat_1(A, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t177_funct_1)).
% 5.85/2.12  tff(f_68, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 5.85/2.12  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.85/2.12  tff(f_97, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 5.85/2.12  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 5.85/2.12  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 5.85/2.12  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.85/2.12  tff(c_70, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_181])).
% 5.85/2.12  tff(c_74, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_181])).
% 5.85/2.12  tff(c_72, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_181])).
% 5.85/2.12  tff(c_76, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_181])).
% 5.85/2.12  tff(c_80, plain, (![A_50]: (u1_struct_0(A_50)=k2_struct_0(A_50) | ~l1_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.85/2.12  tff(c_88, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_76, c_80])).
% 5.85/2.12  tff(c_87, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_72, c_80])).
% 5.85/2.12  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_181])).
% 5.85/2.12  tff(c_123, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_87, c_66])).
% 5.85/2.12  tff(c_2709, plain, (![A_283, B_284, C_285]: (k2_relset_1(A_283, B_284, C_285)=k2_relat_1(C_285) | ~m1_subset_1(C_285, k1_zfmisc_1(k2_zfmisc_1(A_283, B_284))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.85/2.12  tff(c_2717, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_123, c_2709])).
% 5.85/2.12  tff(c_64, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_181])).
% 5.85/2.12  tff(c_118, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_87, c_64])).
% 5.85/2.12  tff(c_2719, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2717, c_118])).
% 5.85/2.12  tff(c_56, plain, (![A_39]: (~v1_xboole_0(k2_struct_0(A_39)) | ~l1_struct_0(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_145])).
% 5.85/2.12  tff(c_2737, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2719, c_56])).
% 5.85/2.12  tff(c_2741, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2737])).
% 5.85/2.12  tff(c_2742, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_74, c_2741])).
% 5.85/2.12  tff(c_18, plain, (![A_10, B_11]: (v1_relat_1(k2_zfmisc_1(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.85/2.12  tff(c_12, plain, (![B_7, A_5]: (v1_relat_1(B_7) | ~m1_subset_1(B_7, k1_zfmisc_1(A_5)) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.85/2.12  tff(c_126, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_123, c_12])).
% 5.85/2.12  tff(c_132, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_126])).
% 5.85/2.12  tff(c_177, plain, (![C_68, A_69, B_70]: (v4_relat_1(C_68, A_69) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.85/2.12  tff(c_185, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_123, c_177])).
% 5.85/2.12  tff(c_2590, plain, (![B_268, A_269]: (k1_relat_1(B_268)=A_269 | ~v1_partfun1(B_268, A_269) | ~v4_relat_1(B_268, A_269) | ~v1_relat_1(B_268))), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.85/2.12  tff(c_2599, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_185, c_2590])).
% 5.85/2.12  tff(c_2607, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_2599])).
% 5.85/2.12  tff(c_2609, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_2607])).
% 5.85/2.12  tff(c_68, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_181])).
% 5.85/2.12  tff(c_93, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_68])).
% 5.85/2.12  tff(c_94, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_93])).
% 5.85/2.12  tff(c_2732, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2719, c_94])).
% 5.85/2.12  tff(c_2731, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_2719, c_123])).
% 5.85/2.12  tff(c_46, plain, (![C_35, A_32, B_33]: (v1_partfun1(C_35, A_32) | ~v1_funct_2(C_35, A_32, B_33) | ~v1_funct_1(C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))) | v1_xboole_0(B_33))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.85/2.12  tff(c_2779, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_2731, c_46])).
% 5.85/2.12  tff(c_2800, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_2732, c_2779])).
% 5.85/2.12  tff(c_2802, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2742, c_2609, c_2800])).
% 5.85/2.12  tff(c_2803, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_2607])).
% 5.85/2.12  tff(c_2812, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_2803, c_123])).
% 5.85/2.12  tff(c_3018, plain, (![A_305, B_306, C_307]: (k2_relset_1(A_305, B_306, C_307)=k2_relat_1(C_307) | ~m1_subset_1(C_307, k1_zfmisc_1(k2_zfmisc_1(A_305, B_306))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.85/2.12  tff(c_3026, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2812, c_3018])).
% 5.85/2.12  tff(c_2813, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2803, c_118])).
% 5.85/2.12  tff(c_3038, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3026, c_2813])).
% 5.85/2.12  tff(c_2814, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2803, c_94])).
% 5.85/2.12  tff(c_3046, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3038, c_2814])).
% 5.85/2.12  tff(c_3043, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3038, c_3026])).
% 5.85/2.12  tff(c_62, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_181])).
% 5.85/2.12  tff(c_3047, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_3038, c_2812])).
% 5.85/2.12  tff(c_3382, plain, (![A_335, B_336, C_337]: (k2_tops_2(A_335, B_336, C_337)=k2_funct_1(C_337) | ~v2_funct_1(C_337) | k2_relset_1(A_335, B_336, C_337)!=B_336 | ~m1_subset_1(C_337, k1_zfmisc_1(k2_zfmisc_1(A_335, B_336))) | ~v1_funct_2(C_337, A_335, B_336) | ~v1_funct_1(C_337))), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.85/2.12  tff(c_3385, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_3047, c_3382])).
% 5.85/2.12  tff(c_3392, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_3046, c_3043, c_62, c_3385])).
% 5.85/2.12  tff(c_513, plain, (![A_128, B_129, C_130]: (k2_relset_1(A_128, B_129, C_130)=k2_relat_1(C_130) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.85/2.12  tff(c_521, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_123, c_513])).
% 5.85/2.12  tff(c_523, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_521, c_118])).
% 5.85/2.12  tff(c_540, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_523, c_56])).
% 5.85/2.12  tff(c_544, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_540])).
% 5.85/2.12  tff(c_545, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_74, c_544])).
% 5.85/2.12  tff(c_361, plain, (![B_103, A_104]: (k1_relat_1(B_103)=A_104 | ~v1_partfun1(B_103, A_104) | ~v4_relat_1(B_103, A_104) | ~v1_relat_1(B_103))), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.85/2.12  tff(c_370, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_185, c_361])).
% 5.85/2.12  tff(c_378, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_370])).
% 5.85/2.12  tff(c_379, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_378])).
% 5.85/2.12  tff(c_535, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_523, c_94])).
% 5.85/2.12  tff(c_534, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_523, c_123])).
% 5.85/2.12  tff(c_644, plain, (![C_133, A_134, B_135]: (v1_partfun1(C_133, A_134) | ~v1_funct_2(C_133, A_134, B_135) | ~v1_funct_1(C_133) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))) | v1_xboole_0(B_135))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.85/2.12  tff(c_647, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_534, c_644])).
% 5.85/2.12  tff(c_654, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_535, c_647])).
% 5.85/2.12  tff(c_656, plain, $false, inference(negUnitSimplification, [status(thm)], [c_545, c_379, c_654])).
% 5.85/2.12  tff(c_657, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_378])).
% 5.85/2.12  tff(c_666, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_657, c_123])).
% 5.85/2.12  tff(c_920, plain, (![A_159, B_160, C_161]: (k2_relset_1(A_159, B_160, C_161)=k2_relat_1(C_161) | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(A_159, B_160))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.85/2.12  tff(c_928, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_666, c_920])).
% 5.85/2.12  tff(c_667, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_657, c_118])).
% 5.85/2.12  tff(c_930, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_928, c_667])).
% 5.85/2.12  tff(c_668, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_657, c_94])).
% 5.85/2.12  tff(c_941, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_930, c_668])).
% 5.85/2.12  tff(c_935, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_930, c_928])).
% 5.85/2.12  tff(c_940, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_930, c_666])).
% 5.85/2.12  tff(c_1261, plain, (![A_183, B_184, C_185]: (k2_tops_2(A_183, B_184, C_185)=k2_funct_1(C_185) | ~v2_funct_1(C_185) | k2_relset_1(A_183, B_184, C_185)!=B_184 | ~m1_subset_1(C_185, k1_zfmisc_1(k2_zfmisc_1(A_183, B_184))) | ~v1_funct_2(C_185, A_183, B_184) | ~v1_funct_1(C_185))), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.85/2.12  tff(c_1264, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_940, c_1261])).
% 5.85/2.12  tff(c_1271, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_941, c_935, c_62, c_1264])).
% 5.85/2.12  tff(c_60, plain, (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_181])).
% 5.85/2.12  tff(c_187, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_88, c_87, c_87, c_88, c_88, c_87, c_87, c_60])).
% 5.85/2.12  tff(c_188, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_187])).
% 5.85/2.12  tff(c_661, plain, (k1_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_657, c_657, c_188])).
% 5.85/2.12  tff(c_937, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_930, c_930, c_930, c_661])).
% 5.85/2.12  tff(c_1273, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1271, c_937])).
% 5.85/2.12  tff(c_30, plain, (![A_18]: (v1_relat_1(k2_funct_1(A_18)) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.85/2.12  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.85/2.12  tff(c_211, plain, (![B_77, A_78]: (k7_relat_1(B_77, A_78)=B_77 | ~v4_relat_1(B_77, A_78) | ~v1_relat_1(B_77))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.85/2.12  tff(c_220, plain, (k7_relat_1('#skF_3', k2_struct_0('#skF_1'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_185, c_211])).
% 5.85/2.12  tff(c_227, plain, (k7_relat_1('#skF_3', k2_struct_0('#skF_1'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_132, c_220])).
% 5.85/2.12  tff(c_663, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_657, c_227])).
% 5.85/2.12  tff(c_22, plain, (![B_14, A_13]: (k2_relat_1(k7_relat_1(B_14, A_13))=k9_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.85/2.12  tff(c_709, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_663, c_22])).
% 5.85/2.12  tff(c_719, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_709])).
% 5.85/2.12  tff(c_1129, plain, (![A_175, B_176]: (k9_relat_1(k2_funct_1(A_175), k9_relat_1(A_175, B_176))=B_176 | ~r1_tarski(B_176, k1_relat_1(A_175)) | ~v2_funct_1(A_175) | ~v1_funct_1(A_175) | ~v1_relat_1(A_175))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.85/2.12  tff(c_1144, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k1_relat_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_719, c_1129])).
% 5.85/2.12  tff(c_1154, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_70, c_62, c_6, c_1144])).
% 5.85/2.12  tff(c_26, plain, (![A_17]: (r1_tarski(A_17, k2_zfmisc_1(k1_relat_1(A_17), k2_relat_1(A_17))) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.85/2.12  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.85/2.12  tff(c_294, plain, (![C_86, B_87, A_88]: (v5_relat_1(C_86, B_87) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_88, B_87))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.85/2.12  tff(c_304, plain, (![A_89, B_90, A_91]: (v5_relat_1(A_89, B_90) | ~r1_tarski(A_89, k2_zfmisc_1(A_91, B_90)))), inference(resolution, [status(thm)], [c_10, c_294])).
% 5.85/2.12  tff(c_330, plain, (![A_95]: (v5_relat_1(A_95, k2_relat_1(A_95)) | ~v1_relat_1(A_95))), inference(resolution, [status(thm)], [c_26, c_304])).
% 5.85/2.12  tff(c_1196, plain, (![B_178, A_179]: (v5_relat_1(k7_relat_1(B_178, A_179), k9_relat_1(B_178, A_179)) | ~v1_relat_1(k7_relat_1(B_178, A_179)) | ~v1_relat_1(B_178))), inference(superposition, [status(thm), theory('equality')], [c_22, c_330])).
% 5.85/2.12  tff(c_1202, plain, (v5_relat_1(k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')), k1_relat_1('#skF_3')) | ~v1_relat_1(k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1154, c_1196])).
% 5.85/2.12  tff(c_1296, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1202])).
% 5.85/2.12  tff(c_1299, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_1296])).
% 5.85/2.12  tff(c_1303, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_132, c_70, c_1299])).
% 5.85/2.12  tff(c_1305, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1202])).
% 5.85/2.12  tff(c_36, plain, (![A_22]: (k1_relat_1(k2_funct_1(A_22))=k2_relat_1(A_22) | ~v2_funct_1(A_22) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.85/2.12  tff(c_726, plain, (![A_136]: (k1_relat_1(k2_funct_1(A_136))=k2_relat_1(A_136) | ~v2_funct_1(A_136) | ~v1_funct_1(A_136) | ~v1_relat_1(A_136))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.85/2.12  tff(c_20, plain, (![A_12]: (k9_relat_1(A_12, k1_relat_1(A_12))=k2_relat_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.85/2.12  tff(c_1957, plain, (![A_235]: (k9_relat_1(k2_funct_1(A_235), k2_relat_1(A_235))=k2_relat_1(k2_funct_1(A_235)) | ~v1_relat_1(k2_funct_1(A_235)) | ~v2_funct_1(A_235) | ~v1_funct_1(A_235) | ~v1_relat_1(A_235))), inference(superposition, [status(thm), theory('equality')], [c_726, c_20])).
% 5.85/2.12  tff(c_1969, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1957, c_1154])).
% 5.85/2.12  tff(c_1990, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_70, c_62, c_1305, c_1969])).
% 5.85/2.12  tff(c_2024, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1990, c_26])).
% 5.85/2.12  tff(c_2050, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1305, c_2024])).
% 5.85/2.12  tff(c_186, plain, (![A_3, A_69, B_70]: (v4_relat_1(A_3, A_69) | ~r1_tarski(A_3, k2_zfmisc_1(A_69, B_70)))), inference(resolution, [status(thm)], [c_10, c_177])).
% 5.85/2.12  tff(c_2088, plain, (v4_relat_1(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_2050, c_186])).
% 5.85/2.12  tff(c_2107, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_36, c_2088])).
% 5.85/2.12  tff(c_2124, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_70, c_62, c_2107])).
% 5.85/2.12  tff(c_28, plain, (![A_18]: (v1_funct_1(k2_funct_1(A_18)) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.85/2.12  tff(c_32, plain, (![A_19, B_21]: (k9_relat_1(k2_funct_1(A_19), k9_relat_1(A_19, B_21))=B_21 | ~r1_tarski(B_21, k1_relat_1(A_19)) | ~v2_funct_1(A_19) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.85/2.12  tff(c_1162, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~r1_tarski(k2_relat_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1154, c_32])).
% 5.85/2.12  tff(c_1795, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~r1_tarski(k2_relat_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1305, c_1162])).
% 5.85/2.12  tff(c_1796, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1795])).
% 5.85/2.12  tff(c_1799, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_1796])).
% 5.85/2.12  tff(c_1803, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_132, c_70, c_1799])).
% 5.85/2.12  tff(c_1804, plain, (~v2_funct_1(k2_funct_1('#skF_3')) | ~r1_tarski(k2_relat_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3'))) | k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_1795])).
% 5.85/2.12  tff(c_1924, plain, (~r1_tarski(k2_relat_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_1804])).
% 5.85/2.12  tff(c_1927, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_36, c_1924])).
% 5.85/2.12  tff(c_1930, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_132, c_70, c_62, c_6, c_1927])).
% 5.85/2.12  tff(c_1932, plain, (r1_tarski(k2_relat_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_1804])).
% 5.85/2.12  tff(c_169, plain, (![B_66, A_67]: (r1_tarski(k1_relat_1(B_66), A_67) | ~v4_relat_1(B_66, A_67) | ~v1_relat_1(B_66))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.85/2.12  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.85/2.12  tff(c_175, plain, (![B_66, A_67]: (k1_relat_1(B_66)=A_67 | ~r1_tarski(A_67, k1_relat_1(B_66)) | ~v4_relat_1(B_66, A_67) | ~v1_relat_1(B_66))), inference(resolution, [status(thm)], [c_169, c_2])).
% 5.85/2.12  tff(c_1935, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1932, c_175])).
% 5.85/2.12  tff(c_1946, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1305, c_1935])).
% 5.85/2.12  tff(c_2309, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2124, c_1946])).
% 5.85/2.12  tff(c_868, plain, (![A_152, B_153, C_154]: (k1_relset_1(A_152, B_153, C_154)=k1_relat_1(C_154) | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(A_152, B_153))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.85/2.12  tff(c_882, plain, (![A_155, B_156, A_157]: (k1_relset_1(A_155, B_156, A_157)=k1_relat_1(A_157) | ~r1_tarski(A_157, k2_zfmisc_1(A_155, B_156)))), inference(resolution, [status(thm)], [c_10, c_868])).
% 5.85/2.12  tff(c_900, plain, (![A_17]: (k1_relset_1(k1_relat_1(A_17), k2_relat_1(A_17), A_17)=k1_relat_1(A_17) | ~v1_relat_1(A_17))), inference(resolution, [status(thm)], [c_26, c_882])).
% 5.85/2.12  tff(c_2358, plain, (k1_relset_1(k2_relat_1('#skF_3'), k2_relat_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2309, c_900])).
% 5.85/2.12  tff(c_2411, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1305, c_2309, c_1990, c_2358])).
% 5.85/2.12  tff(c_2413, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1273, c_2411])).
% 5.85/2.12  tff(c_2414, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_187])).
% 5.85/2.12  tff(c_2806, plain, (k2_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2803, c_2803, c_2803, c_2414])).
% 5.85/2.12  tff(c_3338, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3038, c_3038, c_2806])).
% 5.85/2.12  tff(c_3395, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3392, c_3338])).
% 5.85/2.12  tff(c_2437, plain, (![B_243, A_244]: (k7_relat_1(B_243, A_244)=B_243 | ~v4_relat_1(B_243, A_244) | ~v1_relat_1(B_243))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.85/2.12  tff(c_2443, plain, (k7_relat_1('#skF_3', k2_struct_0('#skF_1'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_185, c_2437])).
% 5.85/2.12  tff(c_2449, plain, (k7_relat_1('#skF_3', k2_struct_0('#skF_1'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_132, c_2443])).
% 5.85/2.12  tff(c_2512, plain, (![B_257, A_258]: (k2_relat_1(k7_relat_1(B_257, A_258))=k9_relat_1(B_257, A_258) | ~v1_relat_1(B_257))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.85/2.12  tff(c_2530, plain, (k9_relat_1('#skF_3', k2_struct_0('#skF_1'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2449, c_2512])).
% 5.85/2.12  tff(c_2536, plain, (k9_relat_1('#skF_3', k2_struct_0('#skF_1'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_2530])).
% 5.85/2.12  tff(c_2807, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2803, c_2536])).
% 5.85/2.12  tff(c_3256, plain, (![A_326, B_327]: (k9_relat_1(k2_funct_1(A_326), k9_relat_1(A_326, B_327))=B_327 | ~r1_tarski(B_327, k1_relat_1(A_326)) | ~v2_funct_1(A_326) | ~v1_funct_1(A_326) | ~v1_relat_1(A_326))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.85/2.12  tff(c_3271, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k1_relat_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2807, c_3256])).
% 5.85/2.12  tff(c_3281, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_70, c_62, c_6, c_3271])).
% 5.85/2.12  tff(c_2481, plain, (![C_249, B_250, A_251]: (v5_relat_1(C_249, B_250) | ~m1_subset_1(C_249, k1_zfmisc_1(k2_zfmisc_1(A_251, B_250))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.85/2.12  tff(c_2491, plain, (![A_252, B_253, A_254]: (v5_relat_1(A_252, B_253) | ~r1_tarski(A_252, k2_zfmisc_1(A_254, B_253)))), inference(resolution, [status(thm)], [c_10, c_2481])).
% 5.85/2.12  tff(c_2537, plain, (![A_259]: (v5_relat_1(A_259, k2_relat_1(A_259)) | ~v1_relat_1(A_259))), inference(resolution, [status(thm)], [c_26, c_2491])).
% 5.85/2.12  tff(c_3339, plain, (![B_331, A_332]: (v5_relat_1(k7_relat_1(B_331, A_332), k9_relat_1(B_331, A_332)) | ~v1_relat_1(k7_relat_1(B_331, A_332)) | ~v1_relat_1(B_331))), inference(superposition, [status(thm), theory('equality')], [c_22, c_2537])).
% 5.85/2.12  tff(c_3345, plain, (v5_relat_1(k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')), k1_relat_1('#skF_3')) | ~v1_relat_1(k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3281, c_3339])).
% 5.85/2.12  tff(c_3546, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_3345])).
% 5.85/2.12  tff(c_3549, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_3546])).
% 5.85/2.12  tff(c_3553, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_132, c_70, c_3549])).
% 5.85/2.12  tff(c_3555, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_3345])).
% 5.85/2.12  tff(c_2849, plain, (![A_289]: (k1_relat_1(k2_funct_1(A_289))=k2_relat_1(A_289) | ~v2_funct_1(A_289) | ~v1_funct_1(A_289) | ~v1_relat_1(A_289))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.85/2.12  tff(c_3786, plain, (![A_377]: (k9_relat_1(k2_funct_1(A_377), k2_relat_1(A_377))=k2_relat_1(k2_funct_1(A_377)) | ~v1_relat_1(k2_funct_1(A_377)) | ~v2_funct_1(A_377) | ~v1_funct_1(A_377) | ~v1_relat_1(A_377))), inference(superposition, [status(thm), theory('equality')], [c_2849, c_20])).
% 5.85/2.12  tff(c_3798, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3786, c_3281])).
% 5.85/2.12  tff(c_3819, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_70, c_62, c_3555, c_3798])).
% 5.85/2.12  tff(c_3856, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3819, c_26])).
% 5.85/2.12  tff(c_3884, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_3555, c_3856])).
% 5.85/2.12  tff(c_3987, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_36, c_3884])).
% 5.85/2.12  tff(c_4003, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_70, c_62, c_3987])).
% 5.85/2.12  tff(c_3027, plain, (![A_305, B_306, A_3]: (k2_relset_1(A_305, B_306, A_3)=k2_relat_1(A_3) | ~r1_tarski(A_3, k2_zfmisc_1(A_305, B_306)))), inference(resolution, [status(thm)], [c_10, c_3018])).
% 5.85/2.12  tff(c_4091, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_4003, c_3027])).
% 5.85/2.12  tff(c_4110, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3819, c_4091])).
% 5.85/2.12  tff(c_4112, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3395, c_4110])).
% 5.85/2.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.85/2.12  
% 5.85/2.12  Inference rules
% 5.85/2.12  ----------------------
% 5.85/2.12  #Ref     : 0
% 5.85/2.12  #Sup     : 897
% 5.85/2.12  #Fact    : 0
% 5.85/2.12  #Define  : 0
% 5.85/2.12  #Split   : 26
% 5.85/2.12  #Chain   : 0
% 5.85/2.12  #Close   : 0
% 5.85/2.12  
% 5.85/2.12  Ordering : KBO
% 5.85/2.12  
% 5.85/2.12  Simplification rules
% 5.85/2.12  ----------------------
% 5.85/2.12  #Subsume      : 52
% 5.85/2.12  #Demod        : 726
% 5.85/2.12  #Tautology    : 386
% 5.85/2.12  #SimpNegUnit  : 26
% 5.85/2.12  #BackRed      : 77
% 5.85/2.12  
% 5.85/2.12  #Partial instantiations: 0
% 5.85/2.12  #Strategies tried      : 1
% 5.85/2.12  
% 5.85/2.12  Timing (in seconds)
% 5.85/2.12  ----------------------
% 5.85/2.12  Preprocessing        : 0.35
% 5.85/2.12  Parsing              : 0.18
% 5.85/2.12  CNF conversion       : 0.03
% 5.85/2.12  Main loop            : 0.94
% 5.85/2.12  Inferencing          : 0.33
% 5.85/2.12  Reduction            : 0.33
% 5.85/2.12  Demodulation         : 0.24
% 5.85/2.12  BG Simplification    : 0.04
% 5.85/2.12  Subsumption          : 0.16
% 5.85/2.12  Abstraction          : 0.05
% 5.85/2.12  MUC search           : 0.00
% 5.85/2.12  Cooper               : 0.00
% 5.85/2.12  Total                : 1.37
% 5.85/2.12  Index Insertion      : 0.00
% 5.85/2.13  Index Deletion       : 0.00
% 5.85/2.13  Index Matching       : 0.00
% 5.85/2.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
