%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:33 EST 2020

% Result     : Theorem 3.90s
% Output     : CNFRefutation 3.98s
% Verified   : 
% Statistics : Number of formulae       :  168 (42018 expanded)
%              Number of leaves         :   38 (14840 expanded)
%              Depth                    :   25
%              Number of atoms          :  354 (123732 expanded)
%              Number of equality atoms :  103 (34050 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_167,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).

tff(f_121,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_85,axiom,(
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

tff(f_101,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(f_55,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_47,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_37,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_133,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_145,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_tops_2(A,B,C))
        & v1_funct_2(k2_tops_2(A,B,C),B,A)
        & m1_subset_1(k2_tops_2(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).

tff(f_117,axiom,(
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

tff(c_62,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_68,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_69,plain,(
    ! [A_34] :
      ( u1_struct_0(A_34) = k2_struct_0(A_34)
      | ~ l1_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_77,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_69])).

tff(c_64,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_76,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_69])).

tff(c_58,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_87,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_76,c_58])).

tff(c_89,plain,(
    ! [C_35,A_36,B_37] :
      ( v1_relat_1(C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_93,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_87,c_89])).

tff(c_54,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_163,plain,(
    ! [A_48,B_49,C_50] :
      ( k2_relset_1(A_48,B_49,C_50) = k2_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_167,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_87,c_163])).

tff(c_56,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_94,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_76,c_56])).

tff(c_169,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_94])).

tff(c_60,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_78,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_60])).

tff(c_88,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_78])).

tff(c_177,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_88])).

tff(c_153,plain,(
    ! [A_44,B_45,C_46] :
      ( k1_relset_1(A_44,B_45,C_46) = k1_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_157,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_87,c_153])).

tff(c_175,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_157])).

tff(c_178,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_87])).

tff(c_219,plain,(
    ! [B_60,A_61,C_62] :
      ( k1_xboole_0 = B_60
      | k1_relset_1(A_61,B_60,C_62) = A_61
      | ~ v1_funct_2(C_62,A_61,B_60)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_61,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_222,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_struct_0('#skF_1')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_178,c_219])).

tff(c_225,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_175,c_222])).

tff(c_226,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_225])).

tff(c_230,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_177])).

tff(c_231,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_178])).

tff(c_283,plain,(
    ! [A_66,B_67,D_68] :
      ( r2_funct_2(A_66,B_67,D_68,D_68)
      | ~ m1_subset_1(D_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67)))
      | ~ v1_funct_2(D_68,A_66,B_67)
      | ~ v1_funct_1(D_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_285,plain,
    ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_231,c_283])).

tff(c_288,plain,(
    r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_230,c_285])).

tff(c_12,plain,(
    ! [A_3] :
      ( k2_funct_1(k2_funct_1(A_3)) = A_3
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_8,plain,(
    ! [A_2] :
      ( k2_relat_1(k2_funct_1(A_2)) = k1_relat_1(A_2)
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [A_1] :
      ( v2_funct_1(k2_funct_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_174,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_167])).

tff(c_229,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_174])).

tff(c_374,plain,(
    ! [A_84,B_85,C_86] :
      ( k2_tops_2(A_84,B_85,C_86) = k2_funct_1(C_86)
      | ~ v2_funct_1(C_86)
      | k2_relset_1(A_84,B_85,C_86) != B_85
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85)))
      | ~ v1_funct_2(C_86,A_84,B_85)
      | ~ v1_funct_1(C_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_380,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_231,c_374])).

tff(c_384,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_230,c_229,c_54,c_380])).

tff(c_46,plain,(
    ! [A_27,B_28,C_29] :
      ( m1_subset_1(k2_tops_2(A_27,B_28,C_29),k1_zfmisc_1(k2_zfmisc_1(B_28,A_27)))
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28)))
      | ~ v1_funct_2(C_29,A_27,B_28)
      | ~ v1_funct_1(C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_394,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_384,c_46])).

tff(c_398,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_230,c_231,c_394])).

tff(c_18,plain,(
    ! [A_10,B_11,C_12] :
      ( k2_relset_1(A_10,B_11,C_12) = k2_relat_1(C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_460,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_398,c_18])).

tff(c_341,plain,(
    ! [C_75,A_76,B_77] :
      ( v1_funct_1(k2_funct_1(C_75))
      | k2_relset_1(A_76,B_77,C_75) != B_77
      | ~ v2_funct_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77)))
      | ~ v1_funct_2(C_75,A_76,B_77)
      | ~ v1_funct_1(C_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_347,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_231,c_341])).

tff(c_351,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_230,c_54,c_229,c_347])).

tff(c_363,plain,(
    ! [C_81,B_82,A_83] :
      ( v1_funct_2(k2_funct_1(C_81),B_82,A_83)
      | k2_relset_1(A_83,B_82,C_81) != B_82
      | ~ v2_funct_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_83,B_82)))
      | ~ v1_funct_2(C_81,A_83,B_82)
      | ~ v1_funct_1(C_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_369,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_231,c_363])).

tff(c_373,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_230,c_54,c_229,c_369])).

tff(c_40,plain,(
    ! [C_22,A_20,B_21] :
      ( v1_funct_1(k2_funct_1(C_22))
      | k2_relset_1(A_20,B_21,C_22) != B_21
      | ~ v2_funct_1(C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21)))
      | ~ v1_funct_2(C_22,A_20,B_21)
      | ~ v1_funct_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_411,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_398,c_40])).

tff(c_445,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_351,c_373,c_411])).

tff(c_560,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_460,c_445])).

tff(c_561,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_560])).

tff(c_564,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_561])).

tff(c_568,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_62,c_54,c_564])).

tff(c_569,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_560])).

tff(c_571,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_569])).

tff(c_574,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_571])).

tff(c_578,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_62,c_54,c_574])).

tff(c_580,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_569])).

tff(c_599,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_580,c_460])).

tff(c_570,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_560])).

tff(c_44,plain,(
    ! [A_24,B_25,C_26] :
      ( k2_tops_2(A_24,B_25,C_26) = k2_funct_1(C_26)
      | ~ v2_funct_1(C_26)
      | k2_relset_1(A_24,B_25,C_26) != B_25
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25)))
      | ~ v1_funct_2(C_26,A_24,B_25)
      | ~ v1_funct_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_402,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_398,c_44])).

tff(c_436,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_351,c_373,c_402])).

tff(c_654,plain,(
    k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_599,c_570,c_436])).

tff(c_52,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_140,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_77,c_77,c_76,c_76,c_76,c_52])).

tff(c_176,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_169,c_169,c_140])).

tff(c_227,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_226,c_226,c_176])).

tff(c_387,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_384,c_227])).

tff(c_658,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_654,c_387])).

tff(c_673,plain,
    ( ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_658])).

tff(c_676,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_62,c_54,c_288,c_673])).

tff(c_677,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_225])).

tff(c_682,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_677,c_177])).

tff(c_683,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_677,c_178])).

tff(c_22,plain,(
    ! [C_15,A_13] :
      ( k1_xboole_0 = C_15
      | ~ v1_funct_2(C_15,A_13,k1_xboole_0)
      | k1_xboole_0 = A_13
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_726,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k1_xboole_0)
    | k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_683,c_22])).

tff(c_750,plain,
    ( k1_xboole_0 = '#skF_3'
    | k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_682,c_726])).

tff(c_751,plain,(
    k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_750])).

tff(c_678,plain,(
    k2_struct_0('#skF_1') != k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_225])).

tff(c_757,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_751,c_678])).

tff(c_755,plain,(
    v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_751,c_682])).

tff(c_680,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k1_xboole_0,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_677,c_175])).

tff(c_753,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_751,c_680])).

tff(c_756,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_751,c_683])).

tff(c_28,plain,(
    ! [B_14,C_15] :
      ( k1_relset_1(k1_xboole_0,B_14,C_15) = k1_xboole_0
      | ~ v1_funct_2(C_15,k1_xboole_0,B_14)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_794,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') = k1_xboole_0
    | ~ v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_756,c_28])).

tff(c_827,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_755,c_753,c_794])).

tff(c_829,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_757,c_827])).

tff(c_830,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_750])).

tff(c_835,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_830,c_682])).

tff(c_836,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),'#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_830,c_683])).

tff(c_32,plain,(
    ! [A_16,B_17,D_19] :
      ( r2_funct_2(A_16,B_17,D_19,D_19)
      | ~ m1_subset_1(D_19,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17)))
      | ~ v1_funct_2(D_19,A_16,B_17)
      | ~ v1_funct_1(D_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_875,plain,
    ( r2_funct_2(k2_struct_0('#skF_1'),'#skF_3','#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),'#skF_3')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_836,c_32])).

tff(c_893,plain,(
    r2_funct_2(k2_struct_0('#skF_1'),'#skF_3','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_835,c_875])).

tff(c_831,plain,(
    k2_struct_0('#skF_1') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_750])).

tff(c_850,plain,(
    k2_struct_0('#skF_1') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_830,c_831])).

tff(c_681,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_677,c_677,c_174])).

tff(c_834,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),'#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_830,c_830,c_681])).

tff(c_996,plain,(
    ! [C_128,A_129,B_130] :
      ( v1_funct_1(k2_funct_1(C_128))
      | k2_relset_1(A_129,B_130,C_128) != B_130
      | ~ v2_funct_1(C_128)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130)))
      | ~ v1_funct_2(C_128,A_129,B_130)
      | ~ v1_funct_1(C_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1002,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),'#skF_3','#skF_3') != '#skF_3'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),'#skF_3')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_836,c_996])).

tff(c_1006,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_835,c_54,c_834,c_1002])).

tff(c_1007,plain,(
    ! [C_131,B_132,A_133] :
      ( v1_funct_2(k2_funct_1(C_131),B_132,A_133)
      | k2_relset_1(A_133,B_132,C_131) != B_132
      | ~ v2_funct_1(C_131)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_133,B_132)))
      | ~ v1_funct_2(C_131,A_133,B_132)
      | ~ v1_funct_1(C_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1013,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',k2_struct_0('#skF_1'))
    | k2_relset_1(k2_struct_0('#skF_1'),'#skF_3','#skF_3') != '#skF_3'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),'#skF_3')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_836,c_1007])).

tff(c_1017,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_835,c_54,c_834,c_1013])).

tff(c_1031,plain,(
    ! [A_137,B_138,C_139] :
      ( k2_tops_2(A_137,B_138,C_139) = k2_funct_1(C_139)
      | ~ v2_funct_1(C_139)
      | k2_relset_1(A_137,B_138,C_139) != B_138
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_137,B_138)))
      | ~ v1_funct_2(C_139,A_137,B_138)
      | ~ v1_funct_1(C_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1037,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),'#skF_3','#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),'#skF_3','#skF_3') != '#skF_3'
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),'#skF_3')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_836,c_1031])).

tff(c_1041,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),'#skF_3','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_835,c_834,c_54,c_1037])).

tff(c_1052,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_struct_0('#skF_1'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),'#skF_3')))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),'#skF_3')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1041,c_46])).

tff(c_1056,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_835,c_836,c_1052])).

tff(c_48,plain,(
    ! [A_27,B_28,C_29] :
      ( v1_funct_2(k2_tops_2(A_27,B_28,C_29),B_28,A_27)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28)))
      | ~ v1_funct_2(C_29,A_27,B_28)
      | ~ v1_funct_1(C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_1085,plain,
    ( v1_funct_2(k2_tops_2('#skF_3',k2_struct_0('#skF_1'),k2_funct_1('#skF_3')),k2_struct_0('#skF_1'),'#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1056,c_48])).

tff(c_1129,plain,(
    v1_funct_2(k2_tops_2('#skF_3',k2_struct_0('#skF_1'),k2_funct_1('#skF_3')),k2_struct_0('#skF_1'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1006,c_1017,c_1085])).

tff(c_922,plain,(
    ! [A_112,B_113,C_114] :
      ( m1_subset_1(k2_tops_2(A_112,B_113,C_114),k1_zfmisc_1(k2_zfmisc_1(B_113,A_112)))
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113)))
      | ~ v1_funct_2(C_114,A_112,B_113)
      | ~ v1_funct_1(C_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_844,plain,(
    ! [C_15,A_13] :
      ( C_15 = '#skF_3'
      | ~ v1_funct_2(C_15,A_13,'#skF_3')
      | A_13 = '#skF_3'
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,'#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_830,c_830,c_830,c_830,c_22])).

tff(c_1326,plain,(
    ! [B_157,C_158] :
      ( k2_tops_2('#skF_3',B_157,C_158) = '#skF_3'
      | ~ v1_funct_2(k2_tops_2('#skF_3',B_157,C_158),B_157,'#skF_3')
      | B_157 = '#skF_3'
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_157)))
      | ~ v1_funct_2(C_158,'#skF_3',B_157)
      | ~ v1_funct_1(C_158) ) ),
    inference(resolution,[status(thm)],[c_922,c_844])).

tff(c_1328,plain,
    ( k2_tops_2('#skF_3',k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = '#skF_3'
    | k2_struct_0('#skF_1') = '#skF_3'
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_struct_0('#skF_1'))))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1129,c_1326])).

tff(c_1331,plain,
    ( k2_tops_2('#skF_3',k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = '#skF_3'
    | k2_struct_0('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1006,c_1017,c_1056,c_1328])).

tff(c_1332,plain,(
    k2_tops_2('#skF_3',k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_850,c_1331])).

tff(c_679,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k1_xboole_0,k2_tops_2(k1_xboole_0,k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k1_xboole_0,'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_677,c_677,c_677,c_176])).

tff(c_851,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),'#skF_3',k2_tops_2('#skF_3',k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),'#skF_3','#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_830,c_830,c_830,c_679])).

tff(c_1046,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),'#skF_3',k2_tops_2('#skF_3',k2_struct_0('#skF_1'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1041,c_851])).

tff(c_1336,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),'#skF_3','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1332,c_1046])).

tff(c_1344,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_893,c_1336])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:45:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.90/1.77  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.98/1.79  
% 3.98/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.98/1.79  %$ r2_funct_2 > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.98/1.79  
% 3.98/1.79  %Foreground sorts:
% 3.98/1.79  
% 3.98/1.79  
% 3.98/1.79  %Background operators:
% 3.98/1.79  
% 3.98/1.79  
% 3.98/1.79  %Foreground operators:
% 3.98/1.79  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.98/1.79  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.98/1.79  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.98/1.79  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.98/1.79  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.98/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.98/1.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.98/1.79  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.98/1.79  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 3.98/1.79  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.98/1.79  tff('#skF_2', type, '#skF_2': $i).
% 3.98/1.79  tff('#skF_3', type, '#skF_3': $i).
% 3.98/1.79  tff('#skF_1', type, '#skF_1': $i).
% 3.98/1.79  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.98/1.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.98/1.79  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.98/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.98/1.79  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.98/1.79  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.98/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.98/1.79  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.98/1.79  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.98/1.79  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.98/1.79  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 3.98/1.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.98/1.79  
% 3.98/1.81  tff(f_167, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tops_2)).
% 3.98/1.81  tff(f_121, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.98/1.81  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.98/1.81  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.98/1.81  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.98/1.81  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.98/1.81  tff(f_101, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 3.98/1.81  tff(f_55, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 3.98/1.81  tff(f_47, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 3.98/1.81  tff(f_37, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_funct_1)).
% 3.98/1.81  tff(f_133, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 3.98/1.81  tff(f_145, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v1_funct_1(k2_tops_2(A, B, C)) & v1_funct_2(k2_tops_2(A, B, C), B, A)) & m1_subset_1(k2_tops_2(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_2)).
% 3.98/1.81  tff(f_117, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 3.98/1.81  tff(c_62, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_167])).
% 3.98/1.81  tff(c_68, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_167])).
% 3.98/1.81  tff(c_69, plain, (![A_34]: (u1_struct_0(A_34)=k2_struct_0(A_34) | ~l1_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.98/1.81  tff(c_77, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_68, c_69])).
% 3.98/1.81  tff(c_64, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_167])).
% 3.98/1.81  tff(c_76, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_64, c_69])).
% 3.98/1.81  tff(c_58, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_167])).
% 3.98/1.81  tff(c_87, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_76, c_58])).
% 3.98/1.81  tff(c_89, plain, (![C_35, A_36, B_37]: (v1_relat_1(C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.98/1.81  tff(c_93, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_87, c_89])).
% 3.98/1.81  tff(c_54, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_167])).
% 3.98/1.81  tff(c_163, plain, (![A_48, B_49, C_50]: (k2_relset_1(A_48, B_49, C_50)=k2_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.98/1.81  tff(c_167, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_87, c_163])).
% 3.98/1.81  tff(c_56, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_167])).
% 3.98/1.81  tff(c_94, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_76, c_56])).
% 3.98/1.81  tff(c_169, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_167, c_94])).
% 3.98/1.81  tff(c_60, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_167])).
% 3.98/1.81  tff(c_78, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_60])).
% 3.98/1.81  tff(c_88, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_78])).
% 3.98/1.81  tff(c_177, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_88])).
% 3.98/1.81  tff(c_153, plain, (![A_44, B_45, C_46]: (k1_relset_1(A_44, B_45, C_46)=k1_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.98/1.81  tff(c_157, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_87, c_153])).
% 3.98/1.81  tff(c_175, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_169, c_157])).
% 3.98/1.81  tff(c_178, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_87])).
% 3.98/1.81  tff(c_219, plain, (![B_60, A_61, C_62]: (k1_xboole_0=B_60 | k1_relset_1(A_61, B_60, C_62)=A_61 | ~v1_funct_2(C_62, A_61, B_60) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_61, B_60))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.98/1.81  tff(c_222, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_struct_0('#skF_1') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_178, c_219])).
% 3.98/1.81  tff(c_225, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_177, c_175, c_222])).
% 3.98/1.81  tff(c_226, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_225])).
% 3.98/1.81  tff(c_230, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_226, c_177])).
% 3.98/1.81  tff(c_231, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_226, c_178])).
% 3.98/1.81  tff(c_283, plain, (![A_66, B_67, D_68]: (r2_funct_2(A_66, B_67, D_68, D_68) | ~m1_subset_1(D_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))) | ~v1_funct_2(D_68, A_66, B_67) | ~v1_funct_1(D_68))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.98/1.81  tff(c_285, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_231, c_283])).
% 3.98/1.81  tff(c_288, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_230, c_285])).
% 3.98/1.81  tff(c_12, plain, (![A_3]: (k2_funct_1(k2_funct_1(A_3))=A_3 | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.98/1.81  tff(c_8, plain, (![A_2]: (k2_relat_1(k2_funct_1(A_2))=k1_relat_1(A_2) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.98/1.81  tff(c_2, plain, (![A_1]: (v2_funct_1(k2_funct_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.98/1.81  tff(c_174, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_169, c_167])).
% 3.98/1.81  tff(c_229, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_226, c_174])).
% 3.98/1.81  tff(c_374, plain, (![A_84, B_85, C_86]: (k2_tops_2(A_84, B_85, C_86)=k2_funct_1(C_86) | ~v2_funct_1(C_86) | k2_relset_1(A_84, B_85, C_86)!=B_85 | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))) | ~v1_funct_2(C_86, A_84, B_85) | ~v1_funct_1(C_86))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.98/1.81  tff(c_380, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_231, c_374])).
% 3.98/1.81  tff(c_384, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_230, c_229, c_54, c_380])).
% 3.98/1.81  tff(c_46, plain, (![A_27, B_28, C_29]: (m1_subset_1(k2_tops_2(A_27, B_28, C_29), k1_zfmisc_1(k2_zfmisc_1(B_28, A_27))) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))) | ~v1_funct_2(C_29, A_27, B_28) | ~v1_funct_1(C_29))), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.98/1.81  tff(c_394, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_384, c_46])).
% 3.98/1.81  tff(c_398, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_230, c_231, c_394])).
% 3.98/1.81  tff(c_18, plain, (![A_10, B_11, C_12]: (k2_relset_1(A_10, B_11, C_12)=k2_relat_1(C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.98/1.81  tff(c_460, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_398, c_18])).
% 3.98/1.81  tff(c_341, plain, (![C_75, A_76, B_77]: (v1_funct_1(k2_funct_1(C_75)) | k2_relset_1(A_76, B_77, C_75)!=B_77 | ~v2_funct_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))) | ~v1_funct_2(C_75, A_76, B_77) | ~v1_funct_1(C_75))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.98/1.81  tff(c_347, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_231, c_341])).
% 3.98/1.81  tff(c_351, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_230, c_54, c_229, c_347])).
% 3.98/1.81  tff(c_363, plain, (![C_81, B_82, A_83]: (v1_funct_2(k2_funct_1(C_81), B_82, A_83) | k2_relset_1(A_83, B_82, C_81)!=B_82 | ~v2_funct_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_83, B_82))) | ~v1_funct_2(C_81, A_83, B_82) | ~v1_funct_1(C_81))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.98/1.81  tff(c_369, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_231, c_363])).
% 3.98/1.81  tff(c_373, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_230, c_54, c_229, c_369])).
% 3.98/1.81  tff(c_40, plain, (![C_22, A_20, B_21]: (v1_funct_1(k2_funct_1(C_22)) | k2_relset_1(A_20, B_21, C_22)!=B_21 | ~v2_funct_1(C_22) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))) | ~v1_funct_2(C_22, A_20, B_21) | ~v1_funct_1(C_22))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.98/1.81  tff(c_411, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_398, c_40])).
% 3.98/1.81  tff(c_445, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_351, c_373, c_411])).
% 3.98/1.81  tff(c_560, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_460, c_445])).
% 3.98/1.81  tff(c_561, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_560])).
% 3.98/1.81  tff(c_564, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2, c_561])).
% 3.98/1.81  tff(c_568, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_93, c_62, c_54, c_564])).
% 3.98/1.81  tff(c_569, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_560])).
% 3.98/1.81  tff(c_571, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_569])).
% 3.98/1.81  tff(c_574, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8, c_571])).
% 3.98/1.81  tff(c_578, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_93, c_62, c_54, c_574])).
% 3.98/1.81  tff(c_580, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_569])).
% 3.98/1.81  tff(c_599, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_580, c_460])).
% 3.98/1.81  tff(c_570, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_560])).
% 3.98/1.81  tff(c_44, plain, (![A_24, B_25, C_26]: (k2_tops_2(A_24, B_25, C_26)=k2_funct_1(C_26) | ~v2_funct_1(C_26) | k2_relset_1(A_24, B_25, C_26)!=B_25 | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))) | ~v1_funct_2(C_26, A_24, B_25) | ~v1_funct_1(C_26))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.98/1.81  tff(c_402, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_398, c_44])).
% 3.98/1.81  tff(c_436, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_351, c_373, c_402])).
% 3.98/1.81  tff(c_654, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_599, c_570, c_436])).
% 3.98/1.81  tff(c_52, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_167])).
% 3.98/1.81  tff(c_140, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_77, c_77, c_76, c_76, c_76, c_52])).
% 3.98/1.81  tff(c_176, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_169, c_169, c_169, c_140])).
% 3.98/1.81  tff(c_227, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_226, c_226, c_226, c_176])).
% 3.98/1.81  tff(c_387, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_384, c_227])).
% 3.98/1.81  tff(c_658, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_654, c_387])).
% 3.98/1.81  tff(c_673, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_658])).
% 3.98/1.81  tff(c_676, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_93, c_62, c_54, c_288, c_673])).
% 3.98/1.81  tff(c_677, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_225])).
% 3.98/1.81  tff(c_682, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_677, c_177])).
% 3.98/1.81  tff(c_683, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_677, c_178])).
% 3.98/1.81  tff(c_22, plain, (![C_15, A_13]: (k1_xboole_0=C_15 | ~v1_funct_2(C_15, A_13, k1_xboole_0) | k1_xboole_0=A_13 | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.98/1.81  tff(c_726, plain, (k1_xboole_0='#skF_3' | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k1_xboole_0) | k2_struct_0('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_683, c_22])).
% 3.98/1.81  tff(c_750, plain, (k1_xboole_0='#skF_3' | k2_struct_0('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_682, c_726])).
% 3.98/1.81  tff(c_751, plain, (k2_struct_0('#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_750])).
% 3.98/1.81  tff(c_678, plain, (k2_struct_0('#skF_1')!=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_225])).
% 3.98/1.81  tff(c_757, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_751, c_678])).
% 3.98/1.81  tff(c_755, plain, (v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_751, c_682])).
% 3.98/1.81  tff(c_680, plain, (k1_relset_1(k2_struct_0('#skF_1'), k1_xboole_0, '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_677, c_175])).
% 3.98/1.81  tff(c_753, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_751, c_680])).
% 3.98/1.81  tff(c_756, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_751, c_683])).
% 3.98/1.81  tff(c_28, plain, (![B_14, C_15]: (k1_relset_1(k1_xboole_0, B_14, C_15)=k1_xboole_0 | ~v1_funct_2(C_15, k1_xboole_0, B_14) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_14))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.98/1.81  tff(c_794, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3')=k1_xboole_0 | ~v1_funct_2('#skF_3', k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_756, c_28])).
% 3.98/1.81  tff(c_827, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_755, c_753, c_794])).
% 3.98/1.81  tff(c_829, plain, $false, inference(negUnitSimplification, [status(thm)], [c_757, c_827])).
% 3.98/1.81  tff(c_830, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_750])).
% 3.98/1.81  tff(c_835, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_830, c_682])).
% 3.98/1.81  tff(c_836, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_830, c_683])).
% 3.98/1.81  tff(c_32, plain, (![A_16, B_17, D_19]: (r2_funct_2(A_16, B_17, D_19, D_19) | ~m1_subset_1(D_19, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))) | ~v1_funct_2(D_19, A_16, B_17) | ~v1_funct_1(D_19))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.98/1.81  tff(c_875, plain, (r2_funct_2(k2_struct_0('#skF_1'), '#skF_3', '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), '#skF_3') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_836, c_32])).
% 3.98/1.81  tff(c_893, plain, (r2_funct_2(k2_struct_0('#skF_1'), '#skF_3', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_835, c_875])).
% 3.98/1.81  tff(c_831, plain, (k2_struct_0('#skF_1')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_750])).
% 3.98/1.81  tff(c_850, plain, (k2_struct_0('#skF_1')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_830, c_831])).
% 3.98/1.81  tff(c_681, plain, (k2_relset_1(k2_struct_0('#skF_1'), k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_677, c_677, c_174])).
% 3.98/1.81  tff(c_834, plain, (k2_relset_1(k2_struct_0('#skF_1'), '#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_830, c_830, c_681])).
% 3.98/1.81  tff(c_996, plain, (![C_128, A_129, B_130]: (v1_funct_1(k2_funct_1(C_128)) | k2_relset_1(A_129, B_130, C_128)!=B_130 | ~v2_funct_1(C_128) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))) | ~v1_funct_2(C_128, A_129, B_130) | ~v1_funct_1(C_128))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.98/1.81  tff(c_1002, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), '#skF_3', '#skF_3')!='#skF_3' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), '#skF_3') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_836, c_996])).
% 3.98/1.81  tff(c_1006, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_835, c_54, c_834, c_1002])).
% 3.98/1.81  tff(c_1007, plain, (![C_131, B_132, A_133]: (v1_funct_2(k2_funct_1(C_131), B_132, A_133) | k2_relset_1(A_133, B_132, C_131)!=B_132 | ~v2_funct_1(C_131) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_133, B_132))) | ~v1_funct_2(C_131, A_133, B_132) | ~v1_funct_1(C_131))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.98/1.81  tff(c_1013, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', k2_struct_0('#skF_1')) | k2_relset_1(k2_struct_0('#skF_1'), '#skF_3', '#skF_3')!='#skF_3' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), '#skF_3') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_836, c_1007])).
% 3.98/1.81  tff(c_1017, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_835, c_54, c_834, c_1013])).
% 3.98/1.81  tff(c_1031, plain, (![A_137, B_138, C_139]: (k2_tops_2(A_137, B_138, C_139)=k2_funct_1(C_139) | ~v2_funct_1(C_139) | k2_relset_1(A_137, B_138, C_139)!=B_138 | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_137, B_138))) | ~v1_funct_2(C_139, A_137, B_138) | ~v1_funct_1(C_139))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.98/1.81  tff(c_1037, plain, (k2_tops_2(k2_struct_0('#skF_1'), '#skF_3', '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), '#skF_3', '#skF_3')!='#skF_3' | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), '#skF_3') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_836, c_1031])).
% 3.98/1.81  tff(c_1041, plain, (k2_tops_2(k2_struct_0('#skF_1'), '#skF_3', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_835, c_834, c_54, c_1037])).
% 3.98/1.81  tff(c_1052, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_struct_0('#skF_1')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), '#skF_3'))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), '#skF_3') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1041, c_46])).
% 3.98/1.81  tff(c_1056, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_835, c_836, c_1052])).
% 3.98/1.81  tff(c_48, plain, (![A_27, B_28, C_29]: (v1_funct_2(k2_tops_2(A_27, B_28, C_29), B_28, A_27) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))) | ~v1_funct_2(C_29, A_27, B_28) | ~v1_funct_1(C_29))), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.98/1.81  tff(c_1085, plain, (v1_funct_2(k2_tops_2('#skF_3', k2_struct_0('#skF_1'), k2_funct_1('#skF_3')), k2_struct_0('#skF_1'), '#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1056, c_48])).
% 3.98/1.81  tff(c_1129, plain, (v1_funct_2(k2_tops_2('#skF_3', k2_struct_0('#skF_1'), k2_funct_1('#skF_3')), k2_struct_0('#skF_1'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1006, c_1017, c_1085])).
% 3.98/1.81  tff(c_922, plain, (![A_112, B_113, C_114]: (m1_subset_1(k2_tops_2(A_112, B_113, C_114), k1_zfmisc_1(k2_zfmisc_1(B_113, A_112))) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))) | ~v1_funct_2(C_114, A_112, B_113) | ~v1_funct_1(C_114))), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.98/1.81  tff(c_844, plain, (![C_15, A_13]: (C_15='#skF_3' | ~v1_funct_2(C_15, A_13, '#skF_3') | A_13='#skF_3' | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_830, c_830, c_830, c_830, c_22])).
% 3.98/1.81  tff(c_1326, plain, (![B_157, C_158]: (k2_tops_2('#skF_3', B_157, C_158)='#skF_3' | ~v1_funct_2(k2_tops_2('#skF_3', B_157, C_158), B_157, '#skF_3') | B_157='#skF_3' | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_157))) | ~v1_funct_2(C_158, '#skF_3', B_157) | ~v1_funct_1(C_158))), inference(resolution, [status(thm)], [c_922, c_844])).
% 3.98/1.81  tff(c_1328, plain, (k2_tops_2('#skF_3', k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))='#skF_3' | k2_struct_0('#skF_1')='#skF_3' | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_struct_0('#skF_1')))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1129, c_1326])).
% 3.98/1.81  tff(c_1331, plain, (k2_tops_2('#skF_3', k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))='#skF_3' | k2_struct_0('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1006, c_1017, c_1056, c_1328])).
% 3.98/1.81  tff(c_1332, plain, (k2_tops_2('#skF_3', k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_850, c_1331])).
% 3.98/1.81  tff(c_679, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k1_xboole_0, k2_tops_2(k1_xboole_0, k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k1_xboole_0, '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_677, c_677, c_677, c_176])).
% 3.98/1.81  tff(c_851, plain, (~r2_funct_2(k2_struct_0('#skF_1'), '#skF_3', k2_tops_2('#skF_3', k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), '#skF_3', '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_830, c_830, c_830, c_679])).
% 3.98/1.81  tff(c_1046, plain, (~r2_funct_2(k2_struct_0('#skF_1'), '#skF_3', k2_tops_2('#skF_3', k2_struct_0('#skF_1'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1041, c_851])).
% 3.98/1.81  tff(c_1336, plain, (~r2_funct_2(k2_struct_0('#skF_1'), '#skF_3', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1332, c_1046])).
% 3.98/1.81  tff(c_1344, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_893, c_1336])).
% 3.98/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.98/1.81  
% 3.98/1.81  Inference rules
% 3.98/1.81  ----------------------
% 3.98/1.82  #Ref     : 0
% 3.98/1.82  #Sup     : 282
% 3.98/1.82  #Fact    : 0
% 3.98/1.82  #Define  : 0
% 3.98/1.82  #Split   : 7
% 3.98/1.82  #Chain   : 0
% 3.98/1.82  #Close   : 0
% 3.98/1.82  
% 3.98/1.82  Ordering : KBO
% 3.98/1.82  
% 3.98/1.82  Simplification rules
% 3.98/1.82  ----------------------
% 3.98/1.82  #Subsume      : 18
% 3.98/1.82  #Demod        : 363
% 3.98/1.82  #Tautology    : 156
% 3.98/1.82  #SimpNegUnit  : 8
% 3.98/1.82  #BackRed      : 63
% 3.98/1.82  
% 3.98/1.82  #Partial instantiations: 0
% 3.98/1.82  #Strategies tried      : 1
% 3.98/1.82  
% 3.98/1.82  Timing (in seconds)
% 3.98/1.82  ----------------------
% 3.98/1.82  Preprocessing        : 0.47
% 3.98/1.82  Parsing              : 0.27
% 3.98/1.82  CNF conversion       : 0.02
% 3.98/1.82  Main loop            : 0.49
% 3.98/1.82  Inferencing          : 0.16
% 3.98/1.82  Reduction            : 0.17
% 3.98/1.82  Demodulation         : 0.12
% 3.98/1.82  BG Simplification    : 0.03
% 3.98/1.82  Subsumption          : 0.08
% 3.98/1.82  Abstraction          : 0.03
% 3.98/1.82  MUC search           : 0.00
% 3.98/1.82  Cooper               : 0.00
% 3.98/1.82  Total                : 1.01
% 3.98/1.82  Index Insertion      : 0.00
% 3.98/1.82  Index Deletion       : 0.00
% 3.98/1.82  Index Matching       : 0.00
% 3.98/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
