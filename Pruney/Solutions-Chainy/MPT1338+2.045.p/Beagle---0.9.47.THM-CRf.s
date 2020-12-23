%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:20 EST 2020

% Result     : Theorem 3.62s
% Output     : CNFRefutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :  138 (3708 expanded)
%              Number of leaves         :   38 (1341 expanded)
%              Depth                    :   14
%              Number of atoms          :  239 (11605 expanded)
%              Number of equality atoms :  102 (4393 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k4_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_134,negated_conjecture,(
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

tff(f_90,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_70,axiom,(
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

tff(f_110,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_40,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_86,axiom,(
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

tff(f_98,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_50,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_56,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_57,plain,(
    ! [A_27] :
      ( u1_struct_0(A_27) = k2_struct_0(A_27)
      | ~ l1_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_65,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_57])).

tff(c_52,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_64,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_57])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_112,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_64,c_46])).

tff(c_427,plain,(
    ! [A_79,B_80,C_81] :
      ( k2_relset_1(A_79,B_80,C_81) = k2_relat_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_431,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_112,c_427])).

tff(c_44,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_106,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_64,c_44])).

tff(c_433,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_431,c_106])).

tff(c_48,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_74,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_64,c_48])).

tff(c_442,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_433,c_74])).

tff(c_418,plain,(
    ! [A_76,B_77,C_78] :
      ( k1_relset_1(A_76,B_77,C_78) = k1_relat_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_422,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_112,c_418])).

tff(c_439,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_433,c_422])).

tff(c_440,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_433,c_112])).

tff(c_496,plain,(
    ! [B_92,A_93,C_94] :
      ( k1_xboole_0 = B_92
      | k1_relset_1(A_93,B_92,C_94) = A_93
      | ~ v1_funct_2(C_94,A_93,B_92)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_93,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_499,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_struct_0('#skF_1')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_440,c_496])).

tff(c_502,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_442,c_439,c_499])).

tff(c_503,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_502])).

tff(c_509,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_503,c_442])).

tff(c_438,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_433,c_431])).

tff(c_506,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_503,c_438])).

tff(c_42,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_508,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_503,c_440])).

tff(c_580,plain,(
    ! [A_101,B_102,C_103] :
      ( k2_tops_2(A_101,B_102,C_103) = k2_funct_1(C_103)
      | ~ v2_funct_1(C_103)
      | k2_relset_1(A_101,B_102,C_103) != B_102
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102)))
      | ~ v1_funct_2(C_103,A_101,B_102)
      | ~ v1_funct_1(C_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_583,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_508,c_580])).

tff(c_586,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_509,c_506,c_42,c_583])).

tff(c_148,plain,(
    ! [A_35,B_36,C_37] :
      ( k2_relset_1(A_35,B_36,C_37) = k2_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_152,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_112,c_148])).

tff(c_153,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_106])).

tff(c_161,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_74])).

tff(c_159,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_112])).

tff(c_191,plain,(
    ! [A_38,B_39,C_40] :
      ( k1_relset_1(A_38,B_39,C_40) = k1_relat_1(C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_195,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_159,c_191])).

tff(c_205,plain,(
    ! [B_48,A_49,C_50] :
      ( k1_xboole_0 = B_48
      | k1_relset_1(A_49,B_48,C_50) = A_49
      | ~ v1_funct_2(C_50,A_49,B_48)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_49,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_208,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_struct_0('#skF_1')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_159,c_205])).

tff(c_211,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_195,c_208])).

tff(c_212,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_211])).

tff(c_217,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_161])).

tff(c_158,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_152])).

tff(c_215,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_158])).

tff(c_216,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_159])).

tff(c_283,plain,(
    ! [A_60,B_61,C_62] :
      ( k2_tops_2(A_60,B_61,C_62) = k2_funct_1(C_62)
      | ~ v2_funct_1(C_62)
      | k2_relset_1(A_60,B_61,C_62) != B_61
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61)))
      | ~ v1_funct_2(C_62,A_60,B_61)
      | ~ v1_funct_1(C_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_286,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_216,c_283])).

tff(c_289,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_217,c_215,c_42,c_286])).

tff(c_40,plain,
    ( k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_117,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_65,c_64,c_64,c_65,c_65,c_64,c_64,c_40])).

tff(c_118,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_117])).

tff(c_201,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_153,c_153,c_118])).

tff(c_213,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_212,c_201])).

tff(c_290,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_213])).

tff(c_10,plain,(
    ! [C_5,A_3,B_4] :
      ( v1_relat_1(C_5)
      | ~ m1_subset_1(C_5,k1_zfmisc_1(k2_zfmisc_1(A_3,B_4))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_116,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_112,c_10])).

tff(c_119,plain,(
    ! [A_34] :
      ( k4_relat_1(A_34) = k2_funct_1(A_34)
      | ~ v2_funct_1(A_34)
      | ~ v1_funct_1(A_34)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_122,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_119])).

tff(c_125,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_50,c_122])).

tff(c_6,plain,(
    ! [A_1] :
      ( k1_relat_1(k4_relat_1(A_1)) = k2_relat_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_132,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_6])).

tff(c_138,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_132])).

tff(c_295,plain,(
    ! [C_63,B_64,A_65] :
      ( m1_subset_1(k2_funct_1(C_63),k1_zfmisc_1(k2_zfmisc_1(B_64,A_65)))
      | k2_relset_1(A_65,B_64,C_63) != B_64
      | ~ v2_funct_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_65,B_64)))
      | ~ v1_funct_2(C_63,A_65,B_64)
      | ~ v1_funct_1(C_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_12,plain,(
    ! [A_6,B_7,C_8] :
      ( k1_relset_1(A_6,B_7,C_8) = k1_relat_1(C_8)
      | ~ m1_subset_1(C_8,k1_zfmisc_1(k2_zfmisc_1(A_6,B_7))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_354,plain,(
    ! [B_69,A_70,C_71] :
      ( k1_relset_1(B_69,A_70,k2_funct_1(C_71)) = k1_relat_1(k2_funct_1(C_71))
      | k2_relset_1(A_70,B_69,C_71) != B_69
      | ~ v2_funct_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_70,B_69)))
      | ~ v1_funct_2(C_71,A_70,B_69)
      | ~ v1_funct_1(C_71) ) ),
    inference(resolution,[status(thm)],[c_295,c_12])).

tff(c_360,plain,
    ( k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_216,c_354])).

tff(c_364,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_217,c_42,c_215,c_138,c_360])).

tff(c_366,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_290,c_364])).

tff(c_367,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_93,plain,(
    ! [A_30] :
      ( ~ v1_xboole_0(u1_struct_0(A_30))
      | ~ l1_struct_0(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_99,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_93])).

tff(c_103,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_99])).

tff(c_104,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_103])).

tff(c_160,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_104])).

tff(c_381,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_367,c_160])).

tff(c_386,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_381])).

tff(c_387,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_117])).

tff(c_487,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_433,c_433,c_387])).

tff(c_504,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_503,c_503,c_503,c_487])).

tff(c_587,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_586,c_504])).

tff(c_389,plain,(
    ! [A_75] :
      ( k4_relat_1(A_75) = k2_funct_1(A_75)
      | ~ v2_funct_1(A_75)
      | ~ v1_funct_1(A_75)
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_392,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_389])).

tff(c_395,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_50,c_392])).

tff(c_4,plain,(
    ! [A_1] :
      ( k2_relat_1(k4_relat_1(A_1)) = k1_relat_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_399,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_395,c_4])).

tff(c_406,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_399])).

tff(c_597,plain,(
    ! [C_104,B_105,A_106] :
      ( m1_subset_1(k2_funct_1(C_104),k1_zfmisc_1(k2_zfmisc_1(B_105,A_106)))
      | k2_relset_1(A_106,B_105,C_104) != B_105
      | ~ v2_funct_1(C_104)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_106,B_105)))
      | ~ v1_funct_2(C_104,A_106,B_105)
      | ~ v1_funct_1(C_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_14,plain,(
    ! [A_9,B_10,C_11] :
      ( k2_relset_1(A_9,B_10,C_11) = k2_relat_1(C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_667,plain,(
    ! [B_113,A_114,C_115] :
      ( k2_relset_1(B_113,A_114,k2_funct_1(C_115)) = k2_relat_1(k2_funct_1(C_115))
      | k2_relset_1(A_114,B_113,C_115) != B_113
      | ~ v2_funct_1(C_115)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_114,B_113)))
      | ~ v1_funct_2(C_115,A_114,B_113)
      | ~ v1_funct_1(C_115) ) ),
    inference(resolution,[status(thm)],[c_597,c_14])).

tff(c_673,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_508,c_667])).

tff(c_677,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_509,c_42,c_506,c_406,c_673])).

tff(c_679,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_587,c_677])).

tff(c_680,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_502])).

tff(c_441,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_433,c_104])).

tff(c_689,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_680,c_441])).

tff(c_694,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_689])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:38:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.62/1.70  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.62/1.71  
% 3.62/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.62/1.71  %$ v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k4_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.62/1.71  
% 3.62/1.71  %Foreground sorts:
% 3.62/1.71  
% 3.62/1.71  
% 3.62/1.71  %Background operators:
% 3.62/1.71  
% 3.62/1.71  
% 3.62/1.71  %Foreground operators:
% 3.62/1.71  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.62/1.71  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.62/1.71  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.62/1.71  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.62/1.71  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.62/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.62/1.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.62/1.71  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.62/1.71  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 3.62/1.71  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.62/1.71  tff('#skF_2', type, '#skF_2': $i).
% 3.62/1.71  tff('#skF_3', type, '#skF_3': $i).
% 3.62/1.71  tff('#skF_1', type, '#skF_1': $i).
% 3.62/1.71  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.62/1.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.62/1.71  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.62/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.62/1.71  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.62/1.71  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.62/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.62/1.71  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.62/1.71  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.62/1.71  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.62/1.71  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.62/1.71  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 3.62/1.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.62/1.71  
% 3.62/1.74  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.62/1.74  tff(f_134, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_2)).
% 3.62/1.74  tff(f_90, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.62/1.74  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.62/1.74  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.62/1.74  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.62/1.74  tff(f_110, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 3.62/1.74  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.62/1.74  tff(f_40, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 3.62/1.74  tff(f_32, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 3.62/1.74  tff(f_86, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 3.62/1.74  tff(f_98, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.62/1.74  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.62/1.74  tff(c_50, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.62/1.74  tff(c_56, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.62/1.74  tff(c_57, plain, (![A_27]: (u1_struct_0(A_27)=k2_struct_0(A_27) | ~l1_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.62/1.74  tff(c_65, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_56, c_57])).
% 3.62/1.74  tff(c_52, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.62/1.74  tff(c_64, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_52, c_57])).
% 3.62/1.74  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.62/1.74  tff(c_112, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_64, c_46])).
% 3.62/1.74  tff(c_427, plain, (![A_79, B_80, C_81]: (k2_relset_1(A_79, B_80, C_81)=k2_relat_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.62/1.74  tff(c_431, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_112, c_427])).
% 3.62/1.74  tff(c_44, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.62/1.74  tff(c_106, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_64, c_44])).
% 3.62/1.74  tff(c_433, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_431, c_106])).
% 3.62/1.74  tff(c_48, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.62/1.74  tff(c_74, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_64, c_48])).
% 3.62/1.74  tff(c_442, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_433, c_74])).
% 3.62/1.74  tff(c_418, plain, (![A_76, B_77, C_78]: (k1_relset_1(A_76, B_77, C_78)=k1_relat_1(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.62/1.74  tff(c_422, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_112, c_418])).
% 3.62/1.74  tff(c_439, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_433, c_422])).
% 3.62/1.74  tff(c_440, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_433, c_112])).
% 3.62/1.74  tff(c_496, plain, (![B_92, A_93, C_94]: (k1_xboole_0=B_92 | k1_relset_1(A_93, B_92, C_94)=A_93 | ~v1_funct_2(C_94, A_93, B_92) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_93, B_92))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.62/1.74  tff(c_499, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_struct_0('#skF_1') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_440, c_496])).
% 3.62/1.74  tff(c_502, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_442, c_439, c_499])).
% 3.62/1.74  tff(c_503, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_502])).
% 3.62/1.74  tff(c_509, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_503, c_442])).
% 3.62/1.74  tff(c_438, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_433, c_431])).
% 3.62/1.74  tff(c_506, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_503, c_438])).
% 3.62/1.74  tff(c_42, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.62/1.74  tff(c_508, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_503, c_440])).
% 3.62/1.74  tff(c_580, plain, (![A_101, B_102, C_103]: (k2_tops_2(A_101, B_102, C_103)=k2_funct_1(C_103) | ~v2_funct_1(C_103) | k2_relset_1(A_101, B_102, C_103)!=B_102 | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))) | ~v1_funct_2(C_103, A_101, B_102) | ~v1_funct_1(C_103))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.62/1.74  tff(c_583, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_508, c_580])).
% 3.62/1.74  tff(c_586, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_509, c_506, c_42, c_583])).
% 3.62/1.74  tff(c_148, plain, (![A_35, B_36, C_37]: (k2_relset_1(A_35, B_36, C_37)=k2_relat_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.62/1.74  tff(c_152, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_112, c_148])).
% 3.62/1.74  tff(c_153, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_152, c_106])).
% 3.62/1.74  tff(c_161, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_153, c_74])).
% 3.62/1.74  tff(c_159, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_153, c_112])).
% 3.62/1.74  tff(c_191, plain, (![A_38, B_39, C_40]: (k1_relset_1(A_38, B_39, C_40)=k1_relat_1(C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.62/1.74  tff(c_195, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_159, c_191])).
% 3.62/1.74  tff(c_205, plain, (![B_48, A_49, C_50]: (k1_xboole_0=B_48 | k1_relset_1(A_49, B_48, C_50)=A_49 | ~v1_funct_2(C_50, A_49, B_48) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_49, B_48))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.62/1.74  tff(c_208, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_struct_0('#skF_1') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_159, c_205])).
% 3.62/1.74  tff(c_211, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_161, c_195, c_208])).
% 3.62/1.74  tff(c_212, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_211])).
% 3.62/1.74  tff(c_217, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_212, c_161])).
% 3.62/1.74  tff(c_158, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_153, c_152])).
% 3.62/1.74  tff(c_215, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_212, c_158])).
% 3.62/1.74  tff(c_216, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_212, c_159])).
% 3.62/1.74  tff(c_283, plain, (![A_60, B_61, C_62]: (k2_tops_2(A_60, B_61, C_62)=k2_funct_1(C_62) | ~v2_funct_1(C_62) | k2_relset_1(A_60, B_61, C_62)!=B_61 | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))) | ~v1_funct_2(C_62, A_60, B_61) | ~v1_funct_1(C_62))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.62/1.74  tff(c_286, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_216, c_283])).
% 3.62/1.74  tff(c_289, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_217, c_215, c_42, c_286])).
% 3.62/1.74  tff(c_40, plain, (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.62/1.74  tff(c_117, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_65, c_64, c_64, c_65, c_65, c_64, c_64, c_40])).
% 3.62/1.74  tff(c_118, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_117])).
% 3.62/1.74  tff(c_201, plain, (k1_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_153, c_153, c_153, c_118])).
% 3.62/1.74  tff(c_213, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_212, c_212, c_201])).
% 3.62/1.74  tff(c_290, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_289, c_213])).
% 3.62/1.74  tff(c_10, plain, (![C_5, A_3, B_4]: (v1_relat_1(C_5) | ~m1_subset_1(C_5, k1_zfmisc_1(k2_zfmisc_1(A_3, B_4))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.62/1.74  tff(c_116, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_112, c_10])).
% 3.62/1.74  tff(c_119, plain, (![A_34]: (k4_relat_1(A_34)=k2_funct_1(A_34) | ~v2_funct_1(A_34) | ~v1_funct_1(A_34) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.62/1.74  tff(c_122, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_119])).
% 3.62/1.74  tff(c_125, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_50, c_122])).
% 3.62/1.74  tff(c_6, plain, (![A_1]: (k1_relat_1(k4_relat_1(A_1))=k2_relat_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.62/1.74  tff(c_132, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_125, c_6])).
% 3.62/1.74  tff(c_138, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_132])).
% 3.62/1.74  tff(c_295, plain, (![C_63, B_64, A_65]: (m1_subset_1(k2_funct_1(C_63), k1_zfmisc_1(k2_zfmisc_1(B_64, A_65))) | k2_relset_1(A_65, B_64, C_63)!=B_64 | ~v2_funct_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_65, B_64))) | ~v1_funct_2(C_63, A_65, B_64) | ~v1_funct_1(C_63))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.62/1.74  tff(c_12, plain, (![A_6, B_7, C_8]: (k1_relset_1(A_6, B_7, C_8)=k1_relat_1(C_8) | ~m1_subset_1(C_8, k1_zfmisc_1(k2_zfmisc_1(A_6, B_7))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.62/1.74  tff(c_354, plain, (![B_69, A_70, C_71]: (k1_relset_1(B_69, A_70, k2_funct_1(C_71))=k1_relat_1(k2_funct_1(C_71)) | k2_relset_1(A_70, B_69, C_71)!=B_69 | ~v2_funct_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_70, B_69))) | ~v1_funct_2(C_71, A_70, B_69) | ~v1_funct_1(C_71))), inference(resolution, [status(thm)], [c_295, c_12])).
% 3.62/1.74  tff(c_360, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_216, c_354])).
% 3.62/1.74  tff(c_364, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_217, c_42, c_215, c_138, c_360])).
% 3.62/1.74  tff(c_366, plain, $false, inference(negUnitSimplification, [status(thm)], [c_290, c_364])).
% 3.62/1.74  tff(c_367, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_211])).
% 3.62/1.74  tff(c_54, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.62/1.74  tff(c_93, plain, (![A_30]: (~v1_xboole_0(u1_struct_0(A_30)) | ~l1_struct_0(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.62/1.74  tff(c_99, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_64, c_93])).
% 3.62/1.74  tff(c_103, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_99])).
% 3.62/1.74  tff(c_104, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_54, c_103])).
% 3.62/1.74  tff(c_160, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_153, c_104])).
% 3.62/1.74  tff(c_381, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_367, c_160])).
% 3.62/1.74  tff(c_386, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_381])).
% 3.62/1.74  tff(c_387, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_117])).
% 3.62/1.74  tff(c_487, plain, (k2_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_433, c_433, c_387])).
% 3.62/1.74  tff(c_504, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_503, c_503, c_503, c_487])).
% 3.62/1.74  tff(c_587, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_586, c_504])).
% 3.62/1.74  tff(c_389, plain, (![A_75]: (k4_relat_1(A_75)=k2_funct_1(A_75) | ~v2_funct_1(A_75) | ~v1_funct_1(A_75) | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.62/1.74  tff(c_392, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_389])).
% 3.62/1.74  tff(c_395, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_50, c_392])).
% 3.62/1.74  tff(c_4, plain, (![A_1]: (k2_relat_1(k4_relat_1(A_1))=k1_relat_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.62/1.74  tff(c_399, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_395, c_4])).
% 3.62/1.74  tff(c_406, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_399])).
% 3.62/1.74  tff(c_597, plain, (![C_104, B_105, A_106]: (m1_subset_1(k2_funct_1(C_104), k1_zfmisc_1(k2_zfmisc_1(B_105, A_106))) | k2_relset_1(A_106, B_105, C_104)!=B_105 | ~v2_funct_1(C_104) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_106, B_105))) | ~v1_funct_2(C_104, A_106, B_105) | ~v1_funct_1(C_104))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.62/1.74  tff(c_14, plain, (![A_9, B_10, C_11]: (k2_relset_1(A_9, B_10, C_11)=k2_relat_1(C_11) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.62/1.74  tff(c_667, plain, (![B_113, A_114, C_115]: (k2_relset_1(B_113, A_114, k2_funct_1(C_115))=k2_relat_1(k2_funct_1(C_115)) | k2_relset_1(A_114, B_113, C_115)!=B_113 | ~v2_funct_1(C_115) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_114, B_113))) | ~v1_funct_2(C_115, A_114, B_113) | ~v1_funct_1(C_115))), inference(resolution, [status(thm)], [c_597, c_14])).
% 3.62/1.74  tff(c_673, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_508, c_667])).
% 3.62/1.74  tff(c_677, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_509, c_42, c_506, c_406, c_673])).
% 3.62/1.74  tff(c_679, plain, $false, inference(negUnitSimplification, [status(thm)], [c_587, c_677])).
% 3.62/1.74  tff(c_680, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_502])).
% 3.62/1.74  tff(c_441, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_433, c_104])).
% 3.62/1.74  tff(c_689, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_680, c_441])).
% 3.62/1.74  tff(c_694, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_689])).
% 3.62/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.62/1.74  
% 3.62/1.74  Inference rules
% 3.62/1.74  ----------------------
% 3.62/1.74  #Ref     : 0
% 3.62/1.74  #Sup     : 146
% 3.62/1.74  #Fact    : 0
% 3.62/1.74  #Define  : 0
% 3.62/1.74  #Split   : 4
% 3.62/1.74  #Chain   : 0
% 3.62/1.74  #Close   : 0
% 3.62/1.74  
% 3.62/1.74  Ordering : KBO
% 3.62/1.74  
% 3.62/1.74  Simplification rules
% 3.62/1.74  ----------------------
% 3.62/1.74  #Subsume      : 8
% 3.62/1.74  #Demod        : 172
% 3.62/1.74  #Tautology    : 88
% 3.62/1.74  #SimpNegUnit  : 5
% 3.62/1.74  #BackRed      : 50
% 3.62/1.74  
% 3.62/1.74  #Partial instantiations: 0
% 3.62/1.74  #Strategies tried      : 1
% 3.62/1.74  
% 3.62/1.74  Timing (in seconds)
% 3.62/1.74  ----------------------
% 3.62/1.74  Preprocessing        : 0.45
% 3.62/1.74  Parsing              : 0.24
% 3.62/1.74  CNF conversion       : 0.03
% 3.62/1.74  Main loop            : 0.43
% 3.62/1.74  Inferencing          : 0.15
% 3.62/1.74  Reduction            : 0.14
% 3.62/1.75  Demodulation         : 0.10
% 3.62/1.75  BG Simplification    : 0.03
% 3.62/1.75  Subsumption          : 0.07
% 3.62/1.75  Abstraction          : 0.02
% 3.62/1.75  MUC search           : 0.00
% 3.62/1.75  Cooper               : 0.00
% 3.62/1.75  Total                : 0.94
% 3.62/1.75  Index Insertion      : 0.00
% 3.62/1.75  Index Deletion       : 0.00
% 3.62/1.75  Index Matching       : 0.00
% 3.62/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
