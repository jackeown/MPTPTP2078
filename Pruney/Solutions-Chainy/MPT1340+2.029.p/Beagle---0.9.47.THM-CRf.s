%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:33 EST 2020

% Result     : Theorem 3.22s
% Output     : CNFRefutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :  126 (13133 expanded)
%              Number of leaves         :   40 (4702 expanded)
%              Depth                    :   20
%              Number of atoms          :  278 (39002 expanded)
%              Number of equality atoms :   74 (10530 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_164,negated_conjecture,(
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

tff(f_122,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_86,axiom,(
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

tff(f_102,axiom,(
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

tff(f_56,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_118,axiom,(
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

tff(f_48,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_38,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_142,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_130,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_66,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_67,plain,(
    ! [A_32] :
      ( u1_struct_0(A_32) = k2_struct_0(A_32)
      | ~ l1_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_75,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_67])).

tff(c_62,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_74,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_67])).

tff(c_56,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_104,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_74,c_56])).

tff(c_16,plain,(
    ! [C_6,A_4,B_5] :
      ( v1_relat_1(C_6)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(A_4,B_5))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_108,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_104,c_16])).

tff(c_60,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_52,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_164,plain,(
    ! [A_44,B_45,C_46] :
      ( k2_relset_1(A_44,B_45,C_46) = k2_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_168,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_104,c_164])).

tff(c_54,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_98,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_74,c_54])).

tff(c_169,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_98])).

tff(c_58,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_84,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_74,c_58])).

tff(c_178,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_84])).

tff(c_176,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_104])).

tff(c_208,plain,(
    ! [A_47,B_48,C_49] :
      ( k1_relset_1(A_47,B_48,C_49) = k1_relat_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_212,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_176,c_208])).

tff(c_220,plain,(
    ! [B_56,A_57,C_58] :
      ( k1_xboole_0 = B_56
      | k1_relset_1(A_57,B_56,C_58) = A_57
      | ~ v1_funct_2(C_58,A_57,B_56)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_57,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_223,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_struct_0('#skF_1')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_176,c_220])).

tff(c_226,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_212,c_223])).

tff(c_227,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_226])).

tff(c_232,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_178])).

tff(c_230,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_176])).

tff(c_284,plain,(
    ! [A_62,B_63,D_64] :
      ( r2_funct_2(A_62,B_63,D_64,D_64)
      | ~ m1_subset_1(D_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63)))
      | ~ v1_funct_2(D_64,A_62,B_63)
      | ~ v1_funct_1(D_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_286,plain,
    ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_230,c_284])).

tff(c_289,plain,(
    r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_232,c_286])).

tff(c_14,plain,(
    ! [A_3] :
      ( k2_funct_1(k2_funct_1(A_3)) = A_3
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_174,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_168])).

tff(c_231,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_174])).

tff(c_290,plain,(
    ! [C_65,A_66,B_67] :
      ( v1_funct_1(k2_funct_1(C_65))
      | k2_relset_1(A_66,B_67,C_65) != B_67
      | ~ v2_funct_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67)))
      | ~ v1_funct_2(C_65,A_66,B_67)
      | ~ v1_funct_1(C_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_293,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_230,c_290])).

tff(c_296,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_232,c_52,c_231,c_293])).

tff(c_297,plain,(
    ! [C_68,B_69,A_70] :
      ( v1_funct_2(k2_funct_1(C_68),B_69,A_70)
      | k2_relset_1(A_70,B_69,C_68) != B_69
      | ~ v2_funct_1(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_70,B_69)))
      | ~ v1_funct_2(C_68,A_70,B_69)
      | ~ v1_funct_1(C_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_300,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_230,c_297])).

tff(c_303,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_232,c_52,c_231,c_300])).

tff(c_10,plain,(
    ! [A_2] :
      ( k2_relat_1(k2_funct_1(A_2)) = k1_relat_1(A_2)
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4,plain,(
    ! [A_1] :
      ( v2_funct_1(k2_funct_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_316,plain,(
    ! [C_74,B_75,A_76] :
      ( m1_subset_1(k2_funct_1(C_74),k1_zfmisc_1(k2_zfmisc_1(B_75,A_76)))
      | k2_relset_1(A_76,B_75,C_74) != B_75
      | ~ v2_funct_1(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_76,B_75)))
      | ~ v1_funct_2(C_74,A_76,B_75)
      | ~ v1_funct_1(C_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_20,plain,(
    ! [A_10,B_11,C_12] :
      ( k2_relset_1(A_10,B_11,C_12) = k2_relat_1(C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_381,plain,(
    ! [B_80,A_81,C_82] :
      ( k2_relset_1(B_80,A_81,k2_funct_1(C_82)) = k2_relat_1(k2_funct_1(C_82))
      | k2_relset_1(A_81,B_80,C_82) != B_80
      | ~ v2_funct_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_81,B_80)))
      | ~ v1_funct_2(C_82,A_81,B_80)
      | ~ v1_funct_1(C_82) ) ),
    inference(resolution,[status(thm)],[c_316,c_20])).

tff(c_387,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_230,c_381])).

tff(c_391,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_232,c_52,c_231,c_387])).

tff(c_42,plain,(
    ! [C_22,A_20,B_21] :
      ( v1_funct_1(k2_funct_1(C_22))
      | k2_relset_1(A_20,B_21,C_22) != B_21
      | ~ v2_funct_1(C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21)))
      | ~ v1_funct_2(C_22,A_20,B_21)
      | ~ v1_funct_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_482,plain,(
    ! [C_103,B_104,A_105] :
      ( v1_funct_1(k2_funct_1(k2_funct_1(C_103)))
      | k2_relset_1(B_104,A_105,k2_funct_1(C_103)) != A_105
      | ~ v2_funct_1(k2_funct_1(C_103))
      | ~ v1_funct_2(k2_funct_1(C_103),B_104,A_105)
      | ~ v1_funct_1(k2_funct_1(C_103))
      | k2_relset_1(A_105,B_104,C_103) != B_104
      | ~ v2_funct_1(C_103)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_105,B_104)))
      | ~ v1_funct_2(C_103,A_105,B_104)
      | ~ v1_funct_1(C_103) ) ),
    inference(resolution,[status(thm)],[c_316,c_42])).

tff(c_488,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_230,c_482])).

tff(c_492,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_232,c_52,c_231,c_296,c_303,c_391,c_488])).

tff(c_493,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_492])).

tff(c_496,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_493])).

tff(c_500,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_60,c_52,c_496])).

tff(c_501,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_492])).

tff(c_503,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_501])).

tff(c_506,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_503])).

tff(c_510,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_60,c_52,c_506])).

tff(c_512,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_501])).

tff(c_518,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_512,c_391])).

tff(c_502,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_492])).

tff(c_48,plain,(
    ! [A_25,B_26,C_27] :
      ( k2_tops_2(A_25,B_26,C_27) = k2_funct_1(C_27)
      | ~ v2_funct_1(C_27)
      | k2_relset_1(A_25,B_26,C_27) != B_26
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | ~ v1_funct_2(C_27,A_25,B_26)
      | ~ v1_funct_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_562,plain,(
    ! [B_112,A_113,C_114] :
      ( k2_tops_2(B_112,A_113,k2_funct_1(C_114)) = k2_funct_1(k2_funct_1(C_114))
      | ~ v2_funct_1(k2_funct_1(C_114))
      | k2_relset_1(B_112,A_113,k2_funct_1(C_114)) != A_113
      | ~ v1_funct_2(k2_funct_1(C_114),B_112,A_113)
      | ~ v1_funct_1(k2_funct_1(C_114))
      | k2_relset_1(A_113,B_112,C_114) != B_112
      | ~ v2_funct_1(C_114)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_113,B_112)))
      | ~ v1_funct_2(C_114,A_113,B_112)
      | ~ v1_funct_1(C_114) ) ),
    inference(resolution,[status(thm)],[c_316,c_48])).

tff(c_568,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_230,c_562])).

tff(c_572,plain,(
    k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_232,c_52,c_231,c_296,c_303,c_518,c_502,c_568])).

tff(c_304,plain,(
    ! [A_71,B_72,C_73] :
      ( k2_tops_2(A_71,B_72,C_73) = k2_funct_1(C_73)
      | ~ v2_funct_1(C_73)
      | k2_relset_1(A_71,B_72,C_73) != B_72
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72)))
      | ~ v1_funct_2(C_73,A_71,B_72)
      | ~ v1_funct_1(C_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_307,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_230,c_304])).

tff(c_310,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_232,c_231,c_52,c_307])).

tff(c_50,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_110,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_75,c_75,c_74,c_74,c_74,c_50])).

tff(c_175,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_169,c_169,c_110])).

tff(c_228,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_227,c_227,c_175])).

tff(c_311,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_228])).

tff(c_573,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_572,c_311])).

tff(c_580,plain,
    ( ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_573])).

tff(c_583,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_60,c_52,c_289,c_580])).

tff(c_584,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_226])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_85,plain,(
    ! [A_33] :
      ( ~ v1_xboole_0(u1_struct_0(A_33))
      | ~ l1_struct_0(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_91,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_85])).

tff(c_95,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_91])).

tff(c_96,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_95])).

tff(c_177,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_96])).

tff(c_592,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_584,c_177])).

tff(c_596,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_592])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:55:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.22/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.48  
% 3.22/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.48  %$ r2_funct_2 > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.22/1.48  
% 3.22/1.48  %Foreground sorts:
% 3.22/1.48  
% 3.22/1.48  
% 3.22/1.48  %Background operators:
% 3.22/1.48  
% 3.22/1.48  
% 3.22/1.48  %Foreground operators:
% 3.22/1.48  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.22/1.48  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.22/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.22/1.48  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.22/1.48  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.22/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.22/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.22/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.22/1.48  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 3.22/1.48  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.22/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.22/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.22/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.22/1.48  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.22/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.22/1.48  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.22/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.22/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.22/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.22/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.22/1.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.22/1.48  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.22/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.22/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.22/1.48  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 3.22/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.22/1.48  
% 3.31/1.50  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.31/1.50  tff(f_164, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tops_2)).
% 3.31/1.50  tff(f_122, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.31/1.50  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.31/1.50  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.31/1.50  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.31/1.50  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.31/1.50  tff(f_102, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 3.31/1.50  tff(f_56, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 3.31/1.50  tff(f_118, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 3.31/1.50  tff(f_48, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 3.31/1.50  tff(f_38, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_funct_1)).
% 3.31/1.50  tff(f_142, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 3.31/1.50  tff(f_130, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.31/1.50  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.31/1.50  tff(c_66, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.31/1.50  tff(c_67, plain, (![A_32]: (u1_struct_0(A_32)=k2_struct_0(A_32) | ~l1_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.31/1.50  tff(c_75, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_66, c_67])).
% 3.31/1.50  tff(c_62, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.31/1.50  tff(c_74, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_62, c_67])).
% 3.31/1.50  tff(c_56, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.31/1.50  tff(c_104, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_74, c_56])).
% 3.31/1.50  tff(c_16, plain, (![C_6, A_4, B_5]: (v1_relat_1(C_6) | ~m1_subset_1(C_6, k1_zfmisc_1(k2_zfmisc_1(A_4, B_5))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.31/1.50  tff(c_108, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_104, c_16])).
% 3.31/1.50  tff(c_60, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.31/1.50  tff(c_52, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.31/1.50  tff(c_164, plain, (![A_44, B_45, C_46]: (k2_relset_1(A_44, B_45, C_46)=k2_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.31/1.50  tff(c_168, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_104, c_164])).
% 3.31/1.50  tff(c_54, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.31/1.50  tff(c_98, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_75, c_74, c_54])).
% 3.31/1.50  tff(c_169, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_168, c_98])).
% 3.31/1.50  tff(c_58, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.31/1.50  tff(c_84, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_74, c_58])).
% 3.31/1.50  tff(c_178, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_84])).
% 3.31/1.50  tff(c_176, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_104])).
% 3.31/1.50  tff(c_208, plain, (![A_47, B_48, C_49]: (k1_relset_1(A_47, B_48, C_49)=k1_relat_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.31/1.50  tff(c_212, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_176, c_208])).
% 3.31/1.50  tff(c_220, plain, (![B_56, A_57, C_58]: (k1_xboole_0=B_56 | k1_relset_1(A_57, B_56, C_58)=A_57 | ~v1_funct_2(C_58, A_57, B_56) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_57, B_56))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.31/1.50  tff(c_223, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_struct_0('#skF_1') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_176, c_220])).
% 3.31/1.50  tff(c_226, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_178, c_212, c_223])).
% 3.31/1.50  tff(c_227, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_226])).
% 3.31/1.50  tff(c_232, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_227, c_178])).
% 3.31/1.50  tff(c_230, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_227, c_176])).
% 3.31/1.50  tff(c_284, plain, (![A_62, B_63, D_64]: (r2_funct_2(A_62, B_63, D_64, D_64) | ~m1_subset_1(D_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))) | ~v1_funct_2(D_64, A_62, B_63) | ~v1_funct_1(D_64))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.31/1.50  tff(c_286, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_230, c_284])).
% 3.31/1.50  tff(c_289, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_232, c_286])).
% 3.31/1.50  tff(c_14, plain, (![A_3]: (k2_funct_1(k2_funct_1(A_3))=A_3 | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.31/1.50  tff(c_174, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_169, c_168])).
% 3.31/1.50  tff(c_231, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_227, c_174])).
% 3.31/1.50  tff(c_290, plain, (![C_65, A_66, B_67]: (v1_funct_1(k2_funct_1(C_65)) | k2_relset_1(A_66, B_67, C_65)!=B_67 | ~v2_funct_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))) | ~v1_funct_2(C_65, A_66, B_67) | ~v1_funct_1(C_65))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.31/1.50  tff(c_293, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_230, c_290])).
% 3.31/1.50  tff(c_296, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_232, c_52, c_231, c_293])).
% 3.31/1.50  tff(c_297, plain, (![C_68, B_69, A_70]: (v1_funct_2(k2_funct_1(C_68), B_69, A_70) | k2_relset_1(A_70, B_69, C_68)!=B_69 | ~v2_funct_1(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_70, B_69))) | ~v1_funct_2(C_68, A_70, B_69) | ~v1_funct_1(C_68))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.31/1.50  tff(c_300, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_230, c_297])).
% 3.31/1.50  tff(c_303, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_232, c_52, c_231, c_300])).
% 3.31/1.50  tff(c_10, plain, (![A_2]: (k2_relat_1(k2_funct_1(A_2))=k1_relat_1(A_2) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.31/1.50  tff(c_4, plain, (![A_1]: (v2_funct_1(k2_funct_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.31/1.50  tff(c_316, plain, (![C_74, B_75, A_76]: (m1_subset_1(k2_funct_1(C_74), k1_zfmisc_1(k2_zfmisc_1(B_75, A_76))) | k2_relset_1(A_76, B_75, C_74)!=B_75 | ~v2_funct_1(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_76, B_75))) | ~v1_funct_2(C_74, A_76, B_75) | ~v1_funct_1(C_74))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.31/1.50  tff(c_20, plain, (![A_10, B_11, C_12]: (k2_relset_1(A_10, B_11, C_12)=k2_relat_1(C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.31/1.50  tff(c_381, plain, (![B_80, A_81, C_82]: (k2_relset_1(B_80, A_81, k2_funct_1(C_82))=k2_relat_1(k2_funct_1(C_82)) | k2_relset_1(A_81, B_80, C_82)!=B_80 | ~v2_funct_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_81, B_80))) | ~v1_funct_2(C_82, A_81, B_80) | ~v1_funct_1(C_82))), inference(resolution, [status(thm)], [c_316, c_20])).
% 3.31/1.50  tff(c_387, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_230, c_381])).
% 3.31/1.50  tff(c_391, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_232, c_52, c_231, c_387])).
% 3.31/1.50  tff(c_42, plain, (![C_22, A_20, B_21]: (v1_funct_1(k2_funct_1(C_22)) | k2_relset_1(A_20, B_21, C_22)!=B_21 | ~v2_funct_1(C_22) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))) | ~v1_funct_2(C_22, A_20, B_21) | ~v1_funct_1(C_22))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.31/1.50  tff(c_482, plain, (![C_103, B_104, A_105]: (v1_funct_1(k2_funct_1(k2_funct_1(C_103))) | k2_relset_1(B_104, A_105, k2_funct_1(C_103))!=A_105 | ~v2_funct_1(k2_funct_1(C_103)) | ~v1_funct_2(k2_funct_1(C_103), B_104, A_105) | ~v1_funct_1(k2_funct_1(C_103)) | k2_relset_1(A_105, B_104, C_103)!=B_104 | ~v2_funct_1(C_103) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_105, B_104))) | ~v1_funct_2(C_103, A_105, B_104) | ~v1_funct_1(C_103))), inference(resolution, [status(thm)], [c_316, c_42])).
% 3.31/1.50  tff(c_488, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_230, c_482])).
% 3.31/1.50  tff(c_492, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_232, c_52, c_231, c_296, c_303, c_391, c_488])).
% 3.31/1.50  tff(c_493, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_492])).
% 3.31/1.50  tff(c_496, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4, c_493])).
% 3.31/1.50  tff(c_500, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_108, c_60, c_52, c_496])).
% 3.31/1.50  tff(c_501, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_492])).
% 3.31/1.50  tff(c_503, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_501])).
% 3.31/1.50  tff(c_506, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10, c_503])).
% 3.31/1.50  tff(c_510, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_108, c_60, c_52, c_506])).
% 3.31/1.50  tff(c_512, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_501])).
% 3.31/1.50  tff(c_518, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_512, c_391])).
% 3.31/1.50  tff(c_502, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_492])).
% 3.31/1.50  tff(c_48, plain, (![A_25, B_26, C_27]: (k2_tops_2(A_25, B_26, C_27)=k2_funct_1(C_27) | ~v2_funct_1(C_27) | k2_relset_1(A_25, B_26, C_27)!=B_26 | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | ~v1_funct_2(C_27, A_25, B_26) | ~v1_funct_1(C_27))), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.31/1.50  tff(c_562, plain, (![B_112, A_113, C_114]: (k2_tops_2(B_112, A_113, k2_funct_1(C_114))=k2_funct_1(k2_funct_1(C_114)) | ~v2_funct_1(k2_funct_1(C_114)) | k2_relset_1(B_112, A_113, k2_funct_1(C_114))!=A_113 | ~v1_funct_2(k2_funct_1(C_114), B_112, A_113) | ~v1_funct_1(k2_funct_1(C_114)) | k2_relset_1(A_113, B_112, C_114)!=B_112 | ~v2_funct_1(C_114) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_113, B_112))) | ~v1_funct_2(C_114, A_113, B_112) | ~v1_funct_1(C_114))), inference(resolution, [status(thm)], [c_316, c_48])).
% 3.31/1.50  tff(c_568, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_230, c_562])).
% 3.31/1.50  tff(c_572, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_232, c_52, c_231, c_296, c_303, c_518, c_502, c_568])).
% 3.31/1.50  tff(c_304, plain, (![A_71, B_72, C_73]: (k2_tops_2(A_71, B_72, C_73)=k2_funct_1(C_73) | ~v2_funct_1(C_73) | k2_relset_1(A_71, B_72, C_73)!=B_72 | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))) | ~v1_funct_2(C_73, A_71, B_72) | ~v1_funct_1(C_73))), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.31/1.50  tff(c_307, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_230, c_304])).
% 3.31/1.50  tff(c_310, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_232, c_231, c_52, c_307])).
% 3.31/1.50  tff(c_50, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.31/1.50  tff(c_110, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_75, c_75, c_75, c_74, c_74, c_74, c_50])).
% 3.31/1.50  tff(c_175, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_169, c_169, c_169, c_110])).
% 3.31/1.50  tff(c_228, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_227, c_227, c_227, c_175])).
% 3.31/1.50  tff(c_311, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_310, c_228])).
% 3.31/1.50  tff(c_573, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_572, c_311])).
% 3.31/1.50  tff(c_580, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_14, c_573])).
% 3.31/1.50  tff(c_583, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_108, c_60, c_52, c_289, c_580])).
% 3.31/1.50  tff(c_584, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_226])).
% 3.31/1.50  tff(c_64, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.31/1.50  tff(c_85, plain, (![A_33]: (~v1_xboole_0(u1_struct_0(A_33)) | ~l1_struct_0(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.31/1.50  tff(c_91, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_74, c_85])).
% 3.31/1.50  tff(c_95, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_91])).
% 3.31/1.50  tff(c_96, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_64, c_95])).
% 3.31/1.50  tff(c_177, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_96])).
% 3.31/1.50  tff(c_592, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_584, c_177])).
% 3.31/1.50  tff(c_596, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_592])).
% 3.31/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.50  
% 3.31/1.50  Inference rules
% 3.31/1.50  ----------------------
% 3.31/1.50  #Ref     : 0
% 3.31/1.50  #Sup     : 120
% 3.31/1.50  #Fact    : 0
% 3.31/1.50  #Define  : 0
% 3.31/1.50  #Split   : 5
% 3.31/1.50  #Chain   : 0
% 3.31/1.50  #Close   : 0
% 3.31/1.50  
% 3.31/1.50  Ordering : KBO
% 3.31/1.50  
% 3.31/1.50  Simplification rules
% 3.31/1.50  ----------------------
% 3.31/1.50  #Subsume      : 6
% 3.31/1.50  #Demod        : 149
% 3.31/1.50  #Tautology    : 69
% 3.31/1.50  #SimpNegUnit  : 2
% 3.31/1.50  #BackRed      : 26
% 3.31/1.50  
% 3.31/1.50  #Partial instantiations: 0
% 3.31/1.50  #Strategies tried      : 1
% 3.31/1.50  
% 3.31/1.50  Timing (in seconds)
% 3.31/1.50  ----------------------
% 3.31/1.51  Preprocessing        : 0.36
% 3.31/1.51  Parsing              : 0.18
% 3.31/1.51  CNF conversion       : 0.02
% 3.31/1.51  Main loop            : 0.37
% 3.31/1.51  Inferencing          : 0.13
% 3.31/1.51  Reduction            : 0.12
% 3.31/1.51  Demodulation         : 0.08
% 3.31/1.51  BG Simplification    : 0.03
% 3.31/1.51  Subsumption          : 0.07
% 3.31/1.51  Abstraction          : 0.02
% 3.31/1.51  MUC search           : 0.00
% 3.31/1.51  Cooper               : 0.00
% 3.31/1.51  Total                : 0.77
% 3.31/1.51  Index Insertion      : 0.00
% 3.31/1.51  Index Deletion       : 0.00
% 3.31/1.51  Index Matching       : 0.00
% 3.31/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
