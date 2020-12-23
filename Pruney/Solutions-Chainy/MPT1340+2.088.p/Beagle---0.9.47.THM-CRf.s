%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:43 EST 2020

% Result     : Theorem 3.33s
% Output     : CNFRefutation 3.70s
% Verified   : 
% Statistics : Number of formulae       :  164 (24558 expanded)
%              Number of leaves         :   44 (8535 expanded)
%              Depth                    :   26
%              Number of atoms          :  421 (70326 expanded)
%              Number of equality atoms :   82 (15197 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_35,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_178,negated_conjecture,(
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

tff(f_136,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_116,axiom,(
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

tff(f_144,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

tff(f_99,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_132,axiom,(
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

tff(f_57,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_47,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_156,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(c_6,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_66,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_68,plain,(
    ! [A_38] :
      ( u1_struct_0(A_38) = k2_struct_0(A_38)
      | ~ l1_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_76,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_68])).

tff(c_62,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_75,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_68])).

tff(c_56,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_89,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_75,c_56])).

tff(c_4,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_92,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_89,c_4])).

tff(c_95,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_92])).

tff(c_60,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_52,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_110,plain,(
    ! [C_48,A_49,B_50] :
      ( v4_relat_1(C_48,A_49)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_114,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_89,c_110])).

tff(c_154,plain,(
    ! [B_54,A_55] :
      ( k1_relat_1(B_54) = A_55
      | ~ v1_partfun1(B_54,A_55)
      | ~ v4_relat_1(B_54,A_55)
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_157,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_114,c_154])).

tff(c_160,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_157])).

tff(c_161,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_160])).

tff(c_177,plain,(
    ! [A_57,B_58,C_59] :
      ( k2_relset_1(A_57,B_58,C_59) = k2_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_181,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_89,c_177])).

tff(c_54,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_96,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_75,c_54])).

tff(c_182,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_96])).

tff(c_58,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_81,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_58])).

tff(c_82,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_81])).

tff(c_191,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_82])).

tff(c_190,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_89])).

tff(c_239,plain,(
    ! [B_65,C_66,A_67] :
      ( k1_xboole_0 = B_65
      | v1_partfun1(C_66,A_67)
      | ~ v1_funct_2(C_66,A_67,B_65)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_65)))
      | ~ v1_funct_1(C_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_242,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_190,c_239])).

tff(c_245,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_191,c_242])).

tff(c_246,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_161,c_245])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_46,plain,(
    ! [A_28] :
      ( ~ v1_xboole_0(k2_struct_0(A_28))
      | ~ l1_struct_0(A_28)
      | v2_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_196,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_46])).

tff(c_200,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_196])).

tff(c_201,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_200])).

tff(c_253,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_201])).

tff(c_257,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_253])).

tff(c_258,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_160])).

tff(c_263,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_89])).

tff(c_329,plain,(
    ! [A_69,B_70,C_71] :
      ( k2_relset_1(A_69,B_70,C_71) = k2_relat_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_333,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_263,c_329])).

tff(c_262,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_96])).

tff(c_334,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_262])).

tff(c_264,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_82])).

tff(c_342,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_264])).

tff(c_341,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_263])).

tff(c_385,plain,(
    ! [A_74,B_75,D_76] :
      ( r2_funct_2(A_74,B_75,D_76,D_76)
      | ~ m1_subset_1(D_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75)))
      | ~ v1_funct_2(D_76,A_74,B_75)
      | ~ v1_funct_1(D_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_387,plain,
    ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_341,c_385])).

tff(c_390,plain,(
    r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_342,c_387])).

tff(c_18,plain,(
    ! [A_8] :
      ( k2_funct_1(k2_funct_1(A_8)) = A_8
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_340,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_333])).

tff(c_408,plain,(
    ! [C_81,A_82,B_83] :
      ( v1_funct_1(k2_funct_1(C_81))
      | k2_relset_1(A_82,B_83,C_81) != B_83
      | ~ v2_funct_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83)))
      | ~ v1_funct_2(C_81,A_82,B_83)
      | ~ v1_funct_1(C_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_411,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_341,c_408])).

tff(c_414,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_342,c_52,c_340,c_411])).

tff(c_415,plain,(
    ! [C_84,B_85,A_86] :
      ( v1_funct_2(k2_funct_1(C_84),B_85,A_86)
      | k2_relset_1(A_86,B_85,C_84) != B_85
      | ~ v2_funct_1(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_86,B_85)))
      | ~ v1_funct_2(C_84,A_86,B_85)
      | ~ v1_funct_1(C_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_418,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_341,c_415])).

tff(c_421,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_342,c_52,c_340,c_418])).

tff(c_14,plain,(
    ! [A_7] :
      ( k2_relat_1(k2_funct_1(A_7)) = k1_relat_1(A_7)
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8,plain,(
    ! [A_6] :
      ( v2_funct_1(k2_funct_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_441,plain,(
    ! [C_91,B_92,A_93] :
      ( m1_subset_1(k2_funct_1(C_91),k1_zfmisc_1(k2_zfmisc_1(B_92,A_93)))
      | k2_relset_1(A_93,B_92,C_91) != B_92
      | ~ v2_funct_1(C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_93,B_92)))
      | ~ v1_funct_2(C_91,A_93,B_92)
      | ~ v1_funct_1(C_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_471,plain,(
    ! [C_91,B_92,A_93] :
      ( v1_relat_1(k2_funct_1(C_91))
      | ~ v1_relat_1(k2_zfmisc_1(B_92,A_93))
      | k2_relset_1(A_93,B_92,C_91) != B_92
      | ~ v2_funct_1(C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_93,B_92)))
      | ~ v1_funct_2(C_91,A_93,B_92)
      | ~ v1_funct_1(C_91) ) ),
    inference(resolution,[status(thm)],[c_441,c_4])).

tff(c_487,plain,(
    ! [C_94,A_95,B_96] :
      ( v1_relat_1(k2_funct_1(C_94))
      | k2_relset_1(A_95,B_96,C_94) != B_96
      | ~ v2_funct_1(C_94)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96)))
      | ~ v1_funct_2(C_94,A_95,B_96)
      | ~ v1_funct_1(C_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_471])).

tff(c_493,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_341,c_487])).

tff(c_497,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_342,c_52,c_340,c_493])).

tff(c_22,plain,(
    ! [C_11,A_9,B_10] :
      ( v4_relat_1(C_11,A_9)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_505,plain,(
    ! [C_101,B_102,A_103] :
      ( v4_relat_1(k2_funct_1(C_101),B_102)
      | k2_relset_1(A_103,B_102,C_101) != B_102
      | ~ v2_funct_1(C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_103,B_102)))
      | ~ v1_funct_2(C_101,A_103,B_102)
      | ~ v1_funct_1(C_101) ) ),
    inference(resolution,[status(thm)],[c_441,c_22])).

tff(c_511,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_341,c_505])).

tff(c_515,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_342,c_52,c_340,c_511])).

tff(c_16,plain,(
    ! [A_7] :
      ( k1_relat_1(k2_funct_1(A_7)) = k2_relat_1(A_7)
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_298,plain,(
    ! [A_68] :
      ( k1_relat_1(k2_funct_1(A_68)) = k2_relat_1(A_68)
      | ~ v2_funct_1(A_68)
      | ~ v1_funct_1(A_68)
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_26,plain,(
    ! [B_16] :
      ( v1_partfun1(B_16,k1_relat_1(B_16))
      | ~ v4_relat_1(B_16,k1_relat_1(B_16))
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_398,plain,(
    ! [A_80] :
      ( v1_partfun1(k2_funct_1(A_80),k1_relat_1(k2_funct_1(A_80)))
      | ~ v4_relat_1(k2_funct_1(A_80),k2_relat_1(A_80))
      | ~ v1_relat_1(k2_funct_1(A_80))
      | ~ v2_funct_1(A_80)
      | ~ v1_funct_1(A_80)
      | ~ v1_relat_1(A_80) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_298,c_26])).

tff(c_401,plain,(
    ! [A_7] :
      ( v1_partfun1(k2_funct_1(A_7),k2_relat_1(A_7))
      | ~ v4_relat_1(k2_funct_1(A_7),k2_relat_1(A_7))
      | ~ v1_relat_1(k2_funct_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7)
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_398])).

tff(c_518,plain,
    ( v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_515,c_401])).

tff(c_524,plain,(
    v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_60,c_52,c_497,c_518])).

tff(c_28,plain,(
    ! [B_16,A_15] :
      ( k1_relat_1(B_16) = A_15
      | ~ v1_partfun1(B_16,A_15)
      | ~ v4_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_521,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_515,c_28])).

tff(c_527,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_497,c_521])).

tff(c_529,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_524,c_527])).

tff(c_588,plain,(
    ! [A_112] :
      ( v1_partfun1(k2_funct_1(k2_funct_1(A_112)),k1_relat_1(A_112))
      | ~ v4_relat_1(k2_funct_1(k2_funct_1(A_112)),k2_relat_1(k2_funct_1(A_112)))
      | ~ v1_relat_1(k2_funct_1(k2_funct_1(A_112)))
      | ~ v2_funct_1(k2_funct_1(A_112))
      | ~ v1_funct_1(k2_funct_1(A_112))
      | ~ v1_relat_1(k2_funct_1(A_112))
      | ~ v2_funct_1(A_112)
      | ~ v1_funct_1(A_112)
      | ~ v1_relat_1(A_112) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_398])).

tff(c_654,plain,(
    ! [A_124] :
      ( v1_partfun1(k2_funct_1(k2_funct_1(A_124)),k1_relat_1(A_124))
      | ~ v4_relat_1(A_124,k2_relat_1(k2_funct_1(A_124)))
      | ~ v1_relat_1(k2_funct_1(k2_funct_1(A_124)))
      | ~ v2_funct_1(k2_funct_1(A_124))
      | ~ v1_funct_1(k2_funct_1(A_124))
      | ~ v1_relat_1(k2_funct_1(A_124))
      | ~ v2_funct_1(A_124)
      | ~ v1_funct_1(A_124)
      | ~ v1_relat_1(A_124)
      | ~ v2_funct_1(A_124)
      | ~ v1_funct_1(A_124)
      | ~ v1_relat_1(A_124) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_588])).

tff(c_657,plain,
    ( v1_partfun1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))),k2_relat_1('#skF_3'))
    | ~ v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_529,c_654])).

tff(c_668,plain,
    ( v1_partfun1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))),k2_relat_1('#skF_3'))
    | ~ v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_497,c_414,c_497,c_414,c_657])).

tff(c_669,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_668])).

tff(c_672,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_669])).

tff(c_676,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_60,c_52,c_672])).

tff(c_678,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_668])).

tff(c_24,plain,(
    ! [A_12,B_13,C_14] :
      ( k2_relset_1(A_12,B_13,C_14) = k2_relat_1(C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_567,plain,(
    ! [B_107,A_108,C_109] :
      ( k2_relset_1(B_107,A_108,k2_funct_1(C_109)) = k2_relat_1(k2_funct_1(C_109))
      | k2_relset_1(A_108,B_107,C_109) != B_107
      | ~ v2_funct_1(C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_108,B_107)))
      | ~ v1_funct_2(C_109,A_108,B_107)
      | ~ v1_funct_1(C_109) ) ),
    inference(resolution,[status(thm)],[c_441,c_24])).

tff(c_573,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_341,c_567])).

tff(c_577,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_342,c_52,c_340,c_573])).

tff(c_42,plain,(
    ! [C_26,A_24,B_25] :
      ( v1_funct_1(k2_funct_1(C_26))
      | k2_relset_1(A_24,B_25,C_26) != B_25
      | ~ v2_funct_1(C_26)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25)))
      | ~ v1_funct_2(C_26,A_24,B_25)
      | ~ v1_funct_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_679,plain,(
    ! [C_125,B_126,A_127] :
      ( v1_funct_1(k2_funct_1(k2_funct_1(C_125)))
      | k2_relset_1(B_126,A_127,k2_funct_1(C_125)) != A_127
      | ~ v2_funct_1(k2_funct_1(C_125))
      | ~ v1_funct_2(k2_funct_1(C_125),B_126,A_127)
      | ~ v1_funct_1(k2_funct_1(C_125))
      | k2_relset_1(A_127,B_126,C_125) != B_126
      | ~ v2_funct_1(C_125)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_127,B_126)))
      | ~ v1_funct_2(C_125,A_127,B_126)
      | ~ v1_funct_1(C_125) ) ),
    inference(resolution,[status(thm)],[c_441,c_42])).

tff(c_685,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_341,c_679])).

tff(c_689,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_342,c_52,c_340,c_414,c_421,c_577,c_685])).

tff(c_691,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_678,c_689])).

tff(c_692,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_691])).

tff(c_695,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_692])).

tff(c_699,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_60,c_52,c_695])).

tff(c_701,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_691])).

tff(c_707,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_701,c_577])).

tff(c_48,plain,(
    ! [A_29,B_30,C_31] :
      ( k2_tops_2(A_29,B_30,C_31) = k2_funct_1(C_31)
      | ~ v2_funct_1(C_31)
      | k2_relset_1(A_29,B_30,C_31) != B_30
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30)))
      | ~ v1_funct_2(C_31,A_29,B_30)
      | ~ v1_funct_1(C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_821,plain,(
    ! [B_131,A_132,C_133] :
      ( k2_tops_2(B_131,A_132,k2_funct_1(C_133)) = k2_funct_1(k2_funct_1(C_133))
      | ~ v2_funct_1(k2_funct_1(C_133))
      | k2_relset_1(B_131,A_132,k2_funct_1(C_133)) != A_132
      | ~ v1_funct_2(k2_funct_1(C_133),B_131,A_132)
      | ~ v1_funct_1(k2_funct_1(C_133))
      | k2_relset_1(A_132,B_131,C_133) != B_131
      | ~ v2_funct_1(C_133)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_132,B_131)))
      | ~ v1_funct_2(C_133,A_132,B_131)
      | ~ v1_funct_1(C_133) ) ),
    inference(resolution,[status(thm)],[c_441,c_48])).

tff(c_827,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_341,c_821])).

tff(c_831,plain,(
    k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_342,c_52,c_340,c_414,c_421,c_707,c_678,c_827])).

tff(c_422,plain,(
    ! [A_87,B_88,C_89] :
      ( k2_tops_2(A_87,B_88,C_89) = k2_funct_1(C_89)
      | ~ v2_funct_1(C_89)
      | k2_relset_1(A_87,B_88,C_89) != B_88
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88)))
      | ~ v1_funct_2(C_89,A_87,B_88)
      | ~ v1_funct_1(C_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_425,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_341,c_422])).

tff(c_428,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_342,c_340,c_52,c_425])).

tff(c_50,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_107,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_76,c_76,c_75,c_75,c_75,c_50])).

tff(c_261,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_258,c_258,c_107])).

tff(c_339,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_334,c_334,c_261])).

tff(c_429,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_428,c_339])).

tff(c_832,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_831,c_429])).

tff(c_839,plain,
    ( ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_832])).

tff(c_842,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_60,c_52,c_390,c_839])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:37:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.33/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.63  
% 3.33/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.64  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.33/1.64  
% 3.33/1.64  %Foreground sorts:
% 3.33/1.64  
% 3.33/1.64  
% 3.33/1.64  %Background operators:
% 3.33/1.64  
% 3.33/1.64  
% 3.33/1.64  %Foreground operators:
% 3.33/1.64  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.33/1.64  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.33/1.64  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.33/1.64  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.33/1.64  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.33/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.33/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.33/1.64  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.33/1.64  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 3.33/1.64  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.33/1.64  tff('#skF_2', type, '#skF_2': $i).
% 3.33/1.64  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.33/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.33/1.64  tff('#skF_1', type, '#skF_1': $i).
% 3.33/1.64  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.33/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.33/1.64  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.33/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.33/1.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.33/1.64  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.33/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.33/1.64  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.33/1.64  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.33/1.64  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.33/1.64  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.33/1.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.33/1.64  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 3.33/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.33/1.64  
% 3.70/1.66  tff(f_35, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.70/1.66  tff(f_178, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tops_2)).
% 3.70/1.66  tff(f_136, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.70/1.66  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.70/1.66  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.70/1.66  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.70/1.66  tff(f_83, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 3.70/1.66  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.70/1.66  tff(f_116, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_funct_2)).
% 3.70/1.66  tff(f_144, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_struct_0)).
% 3.70/1.66  tff(f_99, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 3.70/1.66  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 3.70/1.66  tff(f_132, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 3.70/1.66  tff(f_57, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 3.70/1.66  tff(f_47, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_funct_1)).
% 3.70/1.66  tff(f_156, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 3.70/1.66  tff(c_6, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.70/1.66  tff(c_66, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_178])).
% 3.70/1.66  tff(c_68, plain, (![A_38]: (u1_struct_0(A_38)=k2_struct_0(A_38) | ~l1_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.70/1.66  tff(c_76, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_66, c_68])).
% 3.70/1.66  tff(c_62, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_178])).
% 3.70/1.66  tff(c_75, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_62, c_68])).
% 3.70/1.66  tff(c_56, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_178])).
% 3.70/1.66  tff(c_89, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_75, c_56])).
% 3.70/1.66  tff(c_4, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.70/1.66  tff(c_92, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_89, c_4])).
% 3.70/1.66  tff(c_95, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_92])).
% 3.70/1.66  tff(c_60, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_178])).
% 3.70/1.66  tff(c_52, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_178])).
% 3.70/1.66  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.70/1.66  tff(c_110, plain, (![C_48, A_49, B_50]: (v4_relat_1(C_48, A_49) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.70/1.66  tff(c_114, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_89, c_110])).
% 3.70/1.66  tff(c_154, plain, (![B_54, A_55]: (k1_relat_1(B_54)=A_55 | ~v1_partfun1(B_54, A_55) | ~v4_relat_1(B_54, A_55) | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.70/1.66  tff(c_157, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_114, c_154])).
% 3.70/1.66  tff(c_160, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_157])).
% 3.70/1.66  tff(c_161, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_160])).
% 3.70/1.66  tff(c_177, plain, (![A_57, B_58, C_59]: (k2_relset_1(A_57, B_58, C_59)=k2_relat_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.70/1.66  tff(c_181, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_89, c_177])).
% 3.70/1.66  tff(c_54, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_178])).
% 3.70/1.66  tff(c_96, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_75, c_54])).
% 3.70/1.66  tff(c_182, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_181, c_96])).
% 3.70/1.66  tff(c_58, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_178])).
% 3.70/1.66  tff(c_81, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_58])).
% 3.70/1.66  tff(c_82, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_81])).
% 3.70/1.66  tff(c_191, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_82])).
% 3.70/1.66  tff(c_190, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_89])).
% 3.70/1.66  tff(c_239, plain, (![B_65, C_66, A_67]: (k1_xboole_0=B_65 | v1_partfun1(C_66, A_67) | ~v1_funct_2(C_66, A_67, B_65) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_65))) | ~v1_funct_1(C_66))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.70/1.66  tff(c_242, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_190, c_239])).
% 3.70/1.66  tff(c_245, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_191, c_242])).
% 3.70/1.66  tff(c_246, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_161, c_245])).
% 3.70/1.66  tff(c_64, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_178])).
% 3.70/1.66  tff(c_46, plain, (![A_28]: (~v1_xboole_0(k2_struct_0(A_28)) | ~l1_struct_0(A_28) | v2_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.70/1.66  tff(c_196, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_182, c_46])).
% 3.70/1.66  tff(c_200, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_196])).
% 3.70/1.66  tff(c_201, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_64, c_200])).
% 3.70/1.66  tff(c_253, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_246, c_201])).
% 3.70/1.66  tff(c_257, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_253])).
% 3.70/1.66  tff(c_258, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_160])).
% 3.70/1.66  tff(c_263, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_258, c_89])).
% 3.70/1.66  tff(c_329, plain, (![A_69, B_70, C_71]: (k2_relset_1(A_69, B_70, C_71)=k2_relat_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.70/1.66  tff(c_333, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_263, c_329])).
% 3.70/1.66  tff(c_262, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_258, c_96])).
% 3.70/1.66  tff(c_334, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_333, c_262])).
% 3.70/1.66  tff(c_264, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_258, c_82])).
% 3.70/1.66  tff(c_342, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_334, c_264])).
% 3.70/1.66  tff(c_341, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_334, c_263])).
% 3.70/1.66  tff(c_385, plain, (![A_74, B_75, D_76]: (r2_funct_2(A_74, B_75, D_76, D_76) | ~m1_subset_1(D_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))) | ~v1_funct_2(D_76, A_74, B_75) | ~v1_funct_1(D_76))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.70/1.66  tff(c_387, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_341, c_385])).
% 3.70/1.66  tff(c_390, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_342, c_387])).
% 3.70/1.66  tff(c_18, plain, (![A_8]: (k2_funct_1(k2_funct_1(A_8))=A_8 | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.70/1.66  tff(c_340, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_334, c_333])).
% 3.70/1.66  tff(c_408, plain, (![C_81, A_82, B_83]: (v1_funct_1(k2_funct_1(C_81)) | k2_relset_1(A_82, B_83, C_81)!=B_83 | ~v2_funct_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))) | ~v1_funct_2(C_81, A_82, B_83) | ~v1_funct_1(C_81))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.70/1.66  tff(c_411, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_341, c_408])).
% 3.70/1.66  tff(c_414, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_342, c_52, c_340, c_411])).
% 3.70/1.66  tff(c_415, plain, (![C_84, B_85, A_86]: (v1_funct_2(k2_funct_1(C_84), B_85, A_86) | k2_relset_1(A_86, B_85, C_84)!=B_85 | ~v2_funct_1(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_86, B_85))) | ~v1_funct_2(C_84, A_86, B_85) | ~v1_funct_1(C_84))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.70/1.66  tff(c_418, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_341, c_415])).
% 3.70/1.66  tff(c_421, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_342, c_52, c_340, c_418])).
% 3.70/1.66  tff(c_14, plain, (![A_7]: (k2_relat_1(k2_funct_1(A_7))=k1_relat_1(A_7) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.70/1.66  tff(c_8, plain, (![A_6]: (v2_funct_1(k2_funct_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.70/1.66  tff(c_441, plain, (![C_91, B_92, A_93]: (m1_subset_1(k2_funct_1(C_91), k1_zfmisc_1(k2_zfmisc_1(B_92, A_93))) | k2_relset_1(A_93, B_92, C_91)!=B_92 | ~v2_funct_1(C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_93, B_92))) | ~v1_funct_2(C_91, A_93, B_92) | ~v1_funct_1(C_91))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.70/1.66  tff(c_471, plain, (![C_91, B_92, A_93]: (v1_relat_1(k2_funct_1(C_91)) | ~v1_relat_1(k2_zfmisc_1(B_92, A_93)) | k2_relset_1(A_93, B_92, C_91)!=B_92 | ~v2_funct_1(C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_93, B_92))) | ~v1_funct_2(C_91, A_93, B_92) | ~v1_funct_1(C_91))), inference(resolution, [status(thm)], [c_441, c_4])).
% 3.70/1.66  tff(c_487, plain, (![C_94, A_95, B_96]: (v1_relat_1(k2_funct_1(C_94)) | k2_relset_1(A_95, B_96, C_94)!=B_96 | ~v2_funct_1(C_94) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))) | ~v1_funct_2(C_94, A_95, B_96) | ~v1_funct_1(C_94))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_471])).
% 3.70/1.66  tff(c_493, plain, (v1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_341, c_487])).
% 3.70/1.66  tff(c_497, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_342, c_52, c_340, c_493])).
% 3.70/1.66  tff(c_22, plain, (![C_11, A_9, B_10]: (v4_relat_1(C_11, A_9) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.70/1.66  tff(c_505, plain, (![C_101, B_102, A_103]: (v4_relat_1(k2_funct_1(C_101), B_102) | k2_relset_1(A_103, B_102, C_101)!=B_102 | ~v2_funct_1(C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_103, B_102))) | ~v1_funct_2(C_101, A_103, B_102) | ~v1_funct_1(C_101))), inference(resolution, [status(thm)], [c_441, c_22])).
% 3.70/1.66  tff(c_511, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_341, c_505])).
% 3.70/1.66  tff(c_515, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_342, c_52, c_340, c_511])).
% 3.70/1.66  tff(c_16, plain, (![A_7]: (k1_relat_1(k2_funct_1(A_7))=k2_relat_1(A_7) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.70/1.66  tff(c_298, plain, (![A_68]: (k1_relat_1(k2_funct_1(A_68))=k2_relat_1(A_68) | ~v2_funct_1(A_68) | ~v1_funct_1(A_68) | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.70/1.66  tff(c_26, plain, (![B_16]: (v1_partfun1(B_16, k1_relat_1(B_16)) | ~v4_relat_1(B_16, k1_relat_1(B_16)) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.70/1.66  tff(c_398, plain, (![A_80]: (v1_partfun1(k2_funct_1(A_80), k1_relat_1(k2_funct_1(A_80))) | ~v4_relat_1(k2_funct_1(A_80), k2_relat_1(A_80)) | ~v1_relat_1(k2_funct_1(A_80)) | ~v2_funct_1(A_80) | ~v1_funct_1(A_80) | ~v1_relat_1(A_80))), inference(superposition, [status(thm), theory('equality')], [c_298, c_26])).
% 3.70/1.66  tff(c_401, plain, (![A_7]: (v1_partfun1(k2_funct_1(A_7), k2_relat_1(A_7)) | ~v4_relat_1(k2_funct_1(A_7), k2_relat_1(A_7)) | ~v1_relat_1(k2_funct_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(superposition, [status(thm), theory('equality')], [c_16, c_398])).
% 3.70/1.66  tff(c_518, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_515, c_401])).
% 3.70/1.66  tff(c_524, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_60, c_52, c_497, c_518])).
% 3.70/1.66  tff(c_28, plain, (![B_16, A_15]: (k1_relat_1(B_16)=A_15 | ~v1_partfun1(B_16, A_15) | ~v4_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.70/1.66  tff(c_521, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_515, c_28])).
% 3.70/1.66  tff(c_527, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_497, c_521])).
% 3.70/1.66  tff(c_529, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_524, c_527])).
% 3.70/1.66  tff(c_588, plain, (![A_112]: (v1_partfun1(k2_funct_1(k2_funct_1(A_112)), k1_relat_1(A_112)) | ~v4_relat_1(k2_funct_1(k2_funct_1(A_112)), k2_relat_1(k2_funct_1(A_112))) | ~v1_relat_1(k2_funct_1(k2_funct_1(A_112))) | ~v2_funct_1(k2_funct_1(A_112)) | ~v1_funct_1(k2_funct_1(A_112)) | ~v1_relat_1(k2_funct_1(A_112)) | ~v2_funct_1(A_112) | ~v1_funct_1(A_112) | ~v1_relat_1(A_112))), inference(superposition, [status(thm), theory('equality')], [c_18, c_398])).
% 3.70/1.66  tff(c_654, plain, (![A_124]: (v1_partfun1(k2_funct_1(k2_funct_1(A_124)), k1_relat_1(A_124)) | ~v4_relat_1(A_124, k2_relat_1(k2_funct_1(A_124))) | ~v1_relat_1(k2_funct_1(k2_funct_1(A_124))) | ~v2_funct_1(k2_funct_1(A_124)) | ~v1_funct_1(k2_funct_1(A_124)) | ~v1_relat_1(k2_funct_1(A_124)) | ~v2_funct_1(A_124) | ~v1_funct_1(A_124) | ~v1_relat_1(A_124) | ~v2_funct_1(A_124) | ~v1_funct_1(A_124) | ~v1_relat_1(A_124))), inference(superposition, [status(thm), theory('equality')], [c_18, c_588])).
% 3.70/1.66  tff(c_657, plain, (v1_partfun1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))), k2_relat_1('#skF_3')) | ~v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_529, c_654])).
% 3.70/1.66  tff(c_668, plain, (v1_partfun1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))), k2_relat_1('#skF_3')) | ~v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_497, c_414, c_497, c_414, c_657])).
% 3.70/1.66  tff(c_669, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_668])).
% 3.70/1.66  tff(c_672, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_8, c_669])).
% 3.70/1.66  tff(c_676, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_95, c_60, c_52, c_672])).
% 3.70/1.66  tff(c_678, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_668])).
% 3.70/1.66  tff(c_24, plain, (![A_12, B_13, C_14]: (k2_relset_1(A_12, B_13, C_14)=k2_relat_1(C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.70/1.66  tff(c_567, plain, (![B_107, A_108, C_109]: (k2_relset_1(B_107, A_108, k2_funct_1(C_109))=k2_relat_1(k2_funct_1(C_109)) | k2_relset_1(A_108, B_107, C_109)!=B_107 | ~v2_funct_1(C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_108, B_107))) | ~v1_funct_2(C_109, A_108, B_107) | ~v1_funct_1(C_109))), inference(resolution, [status(thm)], [c_441, c_24])).
% 3.70/1.66  tff(c_573, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_341, c_567])).
% 3.70/1.66  tff(c_577, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_342, c_52, c_340, c_573])).
% 3.70/1.66  tff(c_42, plain, (![C_26, A_24, B_25]: (v1_funct_1(k2_funct_1(C_26)) | k2_relset_1(A_24, B_25, C_26)!=B_25 | ~v2_funct_1(C_26) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))) | ~v1_funct_2(C_26, A_24, B_25) | ~v1_funct_1(C_26))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.70/1.66  tff(c_679, plain, (![C_125, B_126, A_127]: (v1_funct_1(k2_funct_1(k2_funct_1(C_125))) | k2_relset_1(B_126, A_127, k2_funct_1(C_125))!=A_127 | ~v2_funct_1(k2_funct_1(C_125)) | ~v1_funct_2(k2_funct_1(C_125), B_126, A_127) | ~v1_funct_1(k2_funct_1(C_125)) | k2_relset_1(A_127, B_126, C_125)!=B_126 | ~v2_funct_1(C_125) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_127, B_126))) | ~v1_funct_2(C_125, A_127, B_126) | ~v1_funct_1(C_125))), inference(resolution, [status(thm)], [c_441, c_42])).
% 3.70/1.66  tff(c_685, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_341, c_679])).
% 3.70/1.66  tff(c_689, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_342, c_52, c_340, c_414, c_421, c_577, c_685])).
% 3.70/1.66  tff(c_691, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_678, c_689])).
% 3.70/1.66  tff(c_692, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_691])).
% 3.70/1.66  tff(c_695, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_14, c_692])).
% 3.70/1.66  tff(c_699, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_95, c_60, c_52, c_695])).
% 3.70/1.66  tff(c_701, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_691])).
% 3.70/1.66  tff(c_707, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_701, c_577])).
% 3.70/1.66  tff(c_48, plain, (![A_29, B_30, C_31]: (k2_tops_2(A_29, B_30, C_31)=k2_funct_1(C_31) | ~v2_funct_1(C_31) | k2_relset_1(A_29, B_30, C_31)!=B_30 | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))) | ~v1_funct_2(C_31, A_29, B_30) | ~v1_funct_1(C_31))), inference(cnfTransformation, [status(thm)], [f_156])).
% 3.70/1.66  tff(c_821, plain, (![B_131, A_132, C_133]: (k2_tops_2(B_131, A_132, k2_funct_1(C_133))=k2_funct_1(k2_funct_1(C_133)) | ~v2_funct_1(k2_funct_1(C_133)) | k2_relset_1(B_131, A_132, k2_funct_1(C_133))!=A_132 | ~v1_funct_2(k2_funct_1(C_133), B_131, A_132) | ~v1_funct_1(k2_funct_1(C_133)) | k2_relset_1(A_132, B_131, C_133)!=B_131 | ~v2_funct_1(C_133) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_132, B_131))) | ~v1_funct_2(C_133, A_132, B_131) | ~v1_funct_1(C_133))), inference(resolution, [status(thm)], [c_441, c_48])).
% 3.70/1.66  tff(c_827, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_341, c_821])).
% 3.70/1.66  tff(c_831, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_342, c_52, c_340, c_414, c_421, c_707, c_678, c_827])).
% 3.70/1.66  tff(c_422, plain, (![A_87, B_88, C_89]: (k2_tops_2(A_87, B_88, C_89)=k2_funct_1(C_89) | ~v2_funct_1(C_89) | k2_relset_1(A_87, B_88, C_89)!=B_88 | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))) | ~v1_funct_2(C_89, A_87, B_88) | ~v1_funct_1(C_89))), inference(cnfTransformation, [status(thm)], [f_156])).
% 3.70/1.66  tff(c_425, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_341, c_422])).
% 3.70/1.66  tff(c_428, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_342, c_340, c_52, c_425])).
% 3.70/1.66  tff(c_50, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_178])).
% 3.70/1.66  tff(c_107, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_76, c_76, c_75, c_75, c_75, c_50])).
% 3.70/1.66  tff(c_261, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_258, c_258, c_258, c_107])).
% 3.70/1.66  tff(c_339, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_334, c_334, c_334, c_261])).
% 3.70/1.66  tff(c_429, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_428, c_339])).
% 3.70/1.66  tff(c_832, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_831, c_429])).
% 3.70/1.66  tff(c_839, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_18, c_832])).
% 3.70/1.66  tff(c_842, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_95, c_60, c_52, c_390, c_839])).
% 3.70/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/1.66  
% 3.70/1.66  Inference rules
% 3.70/1.66  ----------------------
% 3.70/1.66  #Ref     : 0
% 3.70/1.66  #Sup     : 169
% 3.70/1.66  #Fact    : 0
% 3.70/1.66  #Define  : 0
% 3.70/1.66  #Split   : 7
% 3.70/1.66  #Chain   : 0
% 3.70/1.66  #Close   : 0
% 3.70/1.66  
% 3.70/1.66  Ordering : KBO
% 3.70/1.66  
% 3.70/1.66  Simplification rules
% 3.70/1.66  ----------------------
% 3.70/1.66  #Subsume      : 3
% 3.70/1.66  #Demod        : 242
% 3.70/1.66  #Tautology    : 87
% 3.70/1.66  #SimpNegUnit  : 3
% 3.70/1.66  #BackRed      : 32
% 3.70/1.66  
% 3.70/1.66  #Partial instantiations: 0
% 3.70/1.66  #Strategies tried      : 1
% 3.70/1.66  
% 3.70/1.66  Timing (in seconds)
% 3.70/1.66  ----------------------
% 3.70/1.67  Preprocessing        : 0.37
% 3.70/1.67  Parsing              : 0.20
% 3.70/1.67  CNF conversion       : 0.02
% 3.70/1.67  Main loop            : 0.43
% 3.70/1.67  Inferencing          : 0.15
% 3.70/1.67  Reduction            : 0.14
% 3.70/1.67  Demodulation         : 0.10
% 3.70/1.67  BG Simplification    : 0.02
% 3.70/1.67  Subsumption          : 0.08
% 3.70/1.67  Abstraction          : 0.02
% 3.70/1.67  MUC search           : 0.00
% 3.70/1.67  Cooper               : 0.00
% 3.70/1.67  Total                : 0.85
% 3.70/1.67  Index Insertion      : 0.00
% 3.70/1.67  Index Deletion       : 0.00
% 3.70/1.67  Index Matching       : 0.00
% 3.70/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
