%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:16 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :  126 (1164 expanded)
%              Number of leaves         :   40 ( 428 expanded)
%              Depth                    :   12
%              Number of atoms          :  203 (3558 expanded)
%              Number of equality atoms :   67 (1143 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k3_relset_1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k4_relat_1 > k2_struct_0 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k3_relset_1,type,(
    k3_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_127,negated_conjecture,(
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

tff(f_83,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

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

tff(f_79,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_91,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_33,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k3_relset_1(A,B,C) = k4_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k1_relset_1(B,A,k3_relset_1(A,B,C)) = k2_relset_1(A,B,C)
        & k2_relset_1(B,A,k3_relset_1(A,B,C)) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_relset_1)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_44,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_48,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_49,plain,(
    ! [A_32] :
      ( u1_struct_0(A_32) = k2_struct_0(A_32)
      | ~ l1_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_57,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_49])).

tff(c_56,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_49])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_75,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_56,c_38])).

tff(c_4,plain,(
    ! [C_4,A_2,B_3] :
      ( v1_relat_1(C_4)
      | ~ m1_subset_1(C_4,k1_zfmisc_1(k2_zfmisc_1(A_2,B_3))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_79,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_75,c_4])).

tff(c_80,plain,(
    ! [C_37,A_38,B_39] :
      ( v4_relat_1(C_37,A_38)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_84,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_75,c_80])).

tff(c_285,plain,(
    ! [B_82,A_83] :
      ( k1_relat_1(B_82) = A_83
      | ~ v1_partfun1(B_82,A_83)
      | ~ v4_relat_1(B_82,A_83)
      | ~ v1_relat_1(B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_288,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_285])).

tff(c_291,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_288])).

tff(c_292,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_291])).

tff(c_42,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_40,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_58,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_40])).

tff(c_72,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_58])).

tff(c_325,plain,(
    ! [C_93,A_94,B_95] :
      ( v1_partfun1(C_93,A_94)
      | ~ v1_funct_2(C_93,A_94,B_95)
      | ~ v1_funct_1(C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95)))
      | v1_xboole_0(B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_328,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_75,c_325])).

tff(c_331,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_72,c_328])).

tff(c_332,plain,(
    v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_292,c_331])).

tff(c_28,plain,(
    ! [A_24] :
      ( ~ v1_xboole_0(k2_struct_0(A_24))
      | ~ l1_struct_0(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_335,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_332,c_28])).

tff(c_338,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_335])).

tff(c_340,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_338])).

tff(c_341,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_291])).

tff(c_344,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_341,c_75])).

tff(c_405,plain,(
    ! [A_99,B_100,C_101] :
      ( k1_relset_1(A_99,B_100,C_101) = k1_relat_1(C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_409,plain,(
    k1_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_344,c_405])).

tff(c_34,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_274,plain,(
    ! [A_81] :
      ( k4_relat_1(A_81) = k2_funct_1(A_81)
      | ~ v2_funct_1(A_81)
      | ~ v1_funct_1(A_81)
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_277,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_274])).

tff(c_280,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_42,c_277])).

tff(c_12,plain,(
    ! [A_11,B_12,C_13] :
      ( k3_relset_1(A_11,B_12,C_13) = k4_relat_1(C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_383,plain,(
    k3_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k4_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_344,c_12])).

tff(c_394,plain,(
    k3_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_383])).

tff(c_436,plain,(
    ! [B_108,A_109,C_110] :
      ( k2_relset_1(B_108,A_109,k3_relset_1(A_109,B_108,C_110)) = k1_relset_1(A_109,B_108,C_110)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_109,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_438,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k3_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')) = k1_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_344,c_436])).

tff(c_440,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_409,c_394,c_438])).

tff(c_345,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_341,c_72])).

tff(c_36,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_67,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_56,c_36])).

tff(c_346,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_341,c_67])).

tff(c_445,plain,(
    ! [A_111,B_112,C_113] :
      ( k2_tops_2(A_111,B_112,C_113) = k2_funct_1(C_113)
      | ~ v2_funct_1(C_113)
      | k2_relset_1(A_111,B_112,C_113) != B_112
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112)))
      | ~ v1_funct_2(C_113,A_111,B_112)
      | ~ v1_funct_1(C_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_448,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_344,c_445])).

tff(c_451,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_345,c_346,c_34,c_448])).

tff(c_93,plain,(
    ! [A_44] :
      ( k4_relat_1(A_44) = k2_funct_1(A_44)
      | ~ v2_funct_1(A_44)
      | ~ v1_funct_1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_96,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_93])).

tff(c_99,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_42,c_96])).

tff(c_104,plain,(
    ! [B_45,A_46] :
      ( k1_relat_1(B_45) = A_46
      | ~ v1_partfun1(B_45,A_46)
      | ~ v4_relat_1(B_45,A_46)
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_107,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_104])).

tff(c_110,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_107])).

tff(c_111,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_149,plain,(
    ! [C_59,A_60,B_61] :
      ( v1_partfun1(C_59,A_60)
      | ~ v1_funct_2(C_59,A_60,B_61)
      | ~ v1_funct_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61)))
      | v1_xboole_0(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_152,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_75,c_149])).

tff(c_155,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_72,c_152])).

tff(c_156,plain,(
    v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_155])).

tff(c_159,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_156,c_28])).

tff(c_162,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_159])).

tff(c_164,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_162])).

tff(c_165,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_168,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_75])).

tff(c_228,plain,(
    ! [A_65,B_66,C_67] :
      ( k3_relset_1(A_65,B_66,C_67) = k4_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_231,plain,(
    k3_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k4_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_168,c_228])).

tff(c_233,plain,(
    k3_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_231])).

tff(c_170,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_67])).

tff(c_239,plain,(
    ! [B_68,A_69,C_70] :
      ( k1_relset_1(B_68,A_69,k3_relset_1(A_69,B_68,C_70)) = k2_relset_1(A_69,B_68,C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_69,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_241,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k3_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')) = k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_168,c_239])).

tff(c_243,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_170,c_241])).

tff(c_169,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_72])).

tff(c_260,plain,(
    ! [A_77,B_78,C_79] :
      ( k2_tops_2(A_77,B_78,C_79) = k2_funct_1(C_79)
      | ~ v2_funct_1(C_79)
      | k2_relset_1(A_77,B_78,C_79) != B_78
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78)))
      | ~ v1_funct_2(C_79,A_77,B_78)
      | ~ v1_funct_1(C_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_263,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_168,c_260])).

tff(c_266,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_169,c_170,c_34,c_263])).

tff(c_32,plain,
    ( k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_90,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_57,c_56,c_56,c_57,c_57,c_56,c_56,c_32])).

tff(c_91,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_234,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_165,c_91])).

tff(c_267,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_266,c_234])).

tff(c_270,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_267])).

tff(c_271,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_421,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_341,c_341,c_341,c_271])).

tff(c_453,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_451,c_421])).

tff(c_457,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_440,c_453])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:58:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.78/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.38  
% 2.78/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.39  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k3_relset_1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k4_relat_1 > k2_struct_0 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.78/1.39  
% 2.78/1.39  %Foreground sorts:
% 2.78/1.39  
% 2.78/1.39  
% 2.78/1.39  %Background operators:
% 2.78/1.39  
% 2.78/1.39  
% 2.78/1.39  %Foreground operators:
% 2.78/1.39  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.78/1.39  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.78/1.39  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.78/1.39  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.78/1.39  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.78/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.78/1.39  tff(k3_relset_1, type, k3_relset_1: ($i * $i * $i) > $i).
% 2.78/1.39  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 2.78/1.39  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.78/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.78/1.39  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.78/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.78/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.78/1.39  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.78/1.39  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.78/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.78/1.39  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.78/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.78/1.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.78/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.78/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.78/1.39  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.78/1.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.78/1.39  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.78/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.78/1.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.78/1.39  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.78/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.78/1.39  
% 2.78/1.41  tff(f_127, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_2)).
% 2.78/1.41  tff(f_83, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.78/1.41  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.78/1.41  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.78/1.41  tff(f_79, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 2.78/1.41  tff(f_71, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.78/1.41  tff(f_91, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_struct_0)).
% 2.78/1.41  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.78/1.41  tff(f_33, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 2.78/1.41  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k3_relset_1(A, B, C) = k4_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_relset_1)).
% 2.78/1.41  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k1_relset_1(B, A, k3_relset_1(A, B, C)) = k2_relset_1(A, B, C)) & (k2_relset_1(B, A, k3_relset_1(A, B, C)) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_relset_1)).
% 2.78/1.41  tff(f_103, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 2.78/1.41  tff(c_46, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.78/1.41  tff(c_44, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.78/1.41  tff(c_48, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.78/1.41  tff(c_49, plain, (![A_32]: (u1_struct_0(A_32)=k2_struct_0(A_32) | ~l1_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.78/1.41  tff(c_57, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_48, c_49])).
% 2.78/1.41  tff(c_56, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_49])).
% 2.78/1.41  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.78/1.41  tff(c_75, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_56, c_38])).
% 2.78/1.41  tff(c_4, plain, (![C_4, A_2, B_3]: (v1_relat_1(C_4) | ~m1_subset_1(C_4, k1_zfmisc_1(k2_zfmisc_1(A_2, B_3))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.78/1.41  tff(c_79, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_75, c_4])).
% 2.78/1.41  tff(c_80, plain, (![C_37, A_38, B_39]: (v4_relat_1(C_37, A_38) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.78/1.41  tff(c_84, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_75, c_80])).
% 2.78/1.41  tff(c_285, plain, (![B_82, A_83]: (k1_relat_1(B_82)=A_83 | ~v1_partfun1(B_82, A_83) | ~v4_relat_1(B_82, A_83) | ~v1_relat_1(B_82))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.78/1.41  tff(c_288, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_285])).
% 2.78/1.41  tff(c_291, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_288])).
% 2.78/1.41  tff(c_292, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_291])).
% 2.78/1.41  tff(c_42, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.78/1.41  tff(c_40, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.78/1.41  tff(c_58, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_40])).
% 2.78/1.41  tff(c_72, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_58])).
% 2.78/1.41  tff(c_325, plain, (![C_93, A_94, B_95]: (v1_partfun1(C_93, A_94) | ~v1_funct_2(C_93, A_94, B_95) | ~v1_funct_1(C_93) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))) | v1_xboole_0(B_95))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.78/1.41  tff(c_328, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_75, c_325])).
% 2.78/1.41  tff(c_331, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_72, c_328])).
% 2.78/1.41  tff(c_332, plain, (v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_292, c_331])).
% 2.78/1.41  tff(c_28, plain, (![A_24]: (~v1_xboole_0(k2_struct_0(A_24)) | ~l1_struct_0(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.78/1.41  tff(c_335, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_332, c_28])).
% 2.78/1.41  tff(c_338, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_335])).
% 2.78/1.41  tff(c_340, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_338])).
% 2.78/1.41  tff(c_341, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_291])).
% 2.78/1.41  tff(c_344, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_341, c_75])).
% 2.78/1.41  tff(c_405, plain, (![A_99, B_100, C_101]: (k1_relset_1(A_99, B_100, C_101)=k1_relat_1(C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.78/1.41  tff(c_409, plain, (k1_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_344, c_405])).
% 2.78/1.41  tff(c_34, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.78/1.41  tff(c_274, plain, (![A_81]: (k4_relat_1(A_81)=k2_funct_1(A_81) | ~v2_funct_1(A_81) | ~v1_funct_1(A_81) | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.78/1.41  tff(c_277, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_274])).
% 2.78/1.41  tff(c_280, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_42, c_277])).
% 2.78/1.41  tff(c_12, plain, (![A_11, B_12, C_13]: (k3_relset_1(A_11, B_12, C_13)=k4_relat_1(C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.78/1.41  tff(c_383, plain, (k3_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k4_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_344, c_12])).
% 2.78/1.41  tff(c_394, plain, (k3_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_280, c_383])).
% 2.78/1.41  tff(c_436, plain, (![B_108, A_109, C_110]: (k2_relset_1(B_108, A_109, k3_relset_1(A_109, B_108, C_110))=k1_relset_1(A_109, B_108, C_110) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_109, B_108))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.78/1.41  tff(c_438, plain, (k2_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k3_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3'))=k1_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_344, c_436])).
% 2.78/1.41  tff(c_440, plain, (k2_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_409, c_394, c_438])).
% 2.78/1.41  tff(c_345, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_341, c_72])).
% 2.78/1.41  tff(c_36, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.78/1.41  tff(c_67, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_57, c_56, c_36])).
% 2.78/1.41  tff(c_346, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_341, c_67])).
% 2.78/1.41  tff(c_445, plain, (![A_111, B_112, C_113]: (k2_tops_2(A_111, B_112, C_113)=k2_funct_1(C_113) | ~v2_funct_1(C_113) | k2_relset_1(A_111, B_112, C_113)!=B_112 | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))) | ~v1_funct_2(C_113, A_111, B_112) | ~v1_funct_1(C_113))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.78/1.41  tff(c_448, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_344, c_445])).
% 2.78/1.41  tff(c_451, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_345, c_346, c_34, c_448])).
% 2.78/1.41  tff(c_93, plain, (![A_44]: (k4_relat_1(A_44)=k2_funct_1(A_44) | ~v2_funct_1(A_44) | ~v1_funct_1(A_44) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.78/1.41  tff(c_96, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_93])).
% 2.78/1.41  tff(c_99, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_42, c_96])).
% 2.78/1.41  tff(c_104, plain, (![B_45, A_46]: (k1_relat_1(B_45)=A_46 | ~v1_partfun1(B_45, A_46) | ~v4_relat_1(B_45, A_46) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.78/1.41  tff(c_107, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_104])).
% 2.78/1.41  tff(c_110, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_107])).
% 2.78/1.41  tff(c_111, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_110])).
% 2.78/1.41  tff(c_149, plain, (![C_59, A_60, B_61]: (v1_partfun1(C_59, A_60) | ~v1_funct_2(C_59, A_60, B_61) | ~v1_funct_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))) | v1_xboole_0(B_61))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.78/1.41  tff(c_152, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_75, c_149])).
% 2.78/1.41  tff(c_155, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_72, c_152])).
% 2.78/1.41  tff(c_156, plain, (v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_111, c_155])).
% 2.78/1.41  tff(c_159, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_156, c_28])).
% 2.78/1.41  tff(c_162, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_159])).
% 2.78/1.41  tff(c_164, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_162])).
% 2.78/1.41  tff(c_165, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_110])).
% 2.78/1.41  tff(c_168, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_75])).
% 2.78/1.41  tff(c_228, plain, (![A_65, B_66, C_67]: (k3_relset_1(A_65, B_66, C_67)=k4_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.78/1.41  tff(c_231, plain, (k3_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k4_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_168, c_228])).
% 2.78/1.41  tff(c_233, plain, (k3_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_99, c_231])).
% 2.78/1.41  tff(c_170, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_165, c_67])).
% 2.78/1.41  tff(c_239, plain, (![B_68, A_69, C_70]: (k1_relset_1(B_68, A_69, k3_relset_1(A_69, B_68, C_70))=k2_relset_1(A_69, B_68, C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_69, B_68))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.78/1.41  tff(c_241, plain, (k1_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k3_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3'))=k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_168, c_239])).
% 2.78/1.41  tff(c_243, plain, (k1_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_233, c_170, c_241])).
% 2.78/1.41  tff(c_169, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_72])).
% 2.78/1.41  tff(c_260, plain, (![A_77, B_78, C_79]: (k2_tops_2(A_77, B_78, C_79)=k2_funct_1(C_79) | ~v2_funct_1(C_79) | k2_relset_1(A_77, B_78, C_79)!=B_78 | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))) | ~v1_funct_2(C_79, A_77, B_78) | ~v1_funct_1(C_79))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.78/1.41  tff(c_263, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_168, c_260])).
% 2.78/1.41  tff(c_266, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_169, c_170, c_34, c_263])).
% 2.78/1.41  tff(c_32, plain, (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.78/1.41  tff(c_90, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_57, c_57, c_56, c_56, c_57, c_57, c_56, c_56, c_32])).
% 2.78/1.41  tff(c_91, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_90])).
% 2.78/1.41  tff(c_234, plain, (k1_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_165, c_165, c_91])).
% 2.78/1.41  tff(c_267, plain, (k1_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_266, c_234])).
% 2.78/1.41  tff(c_270, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_243, c_267])).
% 2.78/1.41  tff(c_271, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_90])).
% 2.78/1.41  tff(c_421, plain, (k2_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_341, c_341, c_341, c_271])).
% 2.78/1.41  tff(c_453, plain, (k2_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_451, c_421])).
% 2.78/1.41  tff(c_457, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_440, c_453])).
% 2.78/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.41  
% 2.78/1.41  Inference rules
% 2.78/1.41  ----------------------
% 2.78/1.41  #Ref     : 0
% 2.78/1.41  #Sup     : 98
% 2.78/1.41  #Fact    : 0
% 2.78/1.41  #Define  : 0
% 2.78/1.41  #Split   : 5
% 2.78/1.41  #Chain   : 0
% 2.78/1.41  #Close   : 0
% 2.78/1.41  
% 2.78/1.41  Ordering : KBO
% 2.78/1.41  
% 2.78/1.41  Simplification rules
% 2.78/1.41  ----------------------
% 2.78/1.41  #Subsume      : 0
% 2.78/1.41  #Demod        : 99
% 2.78/1.41  #Tautology    : 68
% 2.78/1.41  #SimpNegUnit  : 4
% 2.78/1.41  #BackRed      : 14
% 2.78/1.41  
% 2.78/1.41  #Partial instantiations: 0
% 2.78/1.41  #Strategies tried      : 1
% 2.78/1.41  
% 2.78/1.41  Timing (in seconds)
% 2.78/1.41  ----------------------
% 2.78/1.41  Preprocessing        : 0.35
% 2.78/1.41  Parsing              : 0.18
% 2.78/1.41  CNF conversion       : 0.02
% 2.78/1.41  Main loop            : 0.28
% 2.78/1.42  Inferencing          : 0.10
% 2.78/1.42  Reduction            : 0.10
% 2.78/1.42  Demodulation         : 0.07
% 2.78/1.42  BG Simplification    : 0.02
% 2.78/1.42  Subsumption          : 0.03
% 2.78/1.42  Abstraction          : 0.02
% 2.78/1.42  MUC search           : 0.00
% 2.78/1.42  Cooper               : 0.00
% 2.78/1.42  Total                : 0.68
% 2.78/1.42  Index Insertion      : 0.00
% 2.78/1.42  Index Deletion       : 0.00
% 2.78/1.42  Index Matching       : 0.00
% 2.78/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
