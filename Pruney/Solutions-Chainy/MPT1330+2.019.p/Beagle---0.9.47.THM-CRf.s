%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:11 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 866 expanded)
%              Number of leaves         :   43 ( 306 expanded)
%              Depth                    :   11
%              Number of atoms          :  197 (2326 expanded)
%              Number of equality atoms :   51 ( 883 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(f_137,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( l1_struct_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( ( k2_struct_0(B) = k1_xboole_0
                   => k2_struct_0(A) = k1_xboole_0 )
                 => k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,k2_struct_0(B)) = k2_struct_0(A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_tops_2)).

tff(f_55,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_118,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_114,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_106,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_92,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F,G] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,G)
                    & r2_hidden(G,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(c_44,plain,
    ( k2_struct_0('#skF_2') = k1_xboole_0
    | k2_struct_0('#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_74,plain,(
    k2_struct_0('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_16,plain,(
    ! [A_12,B_13] : v1_relat_1(k2_zfmisc_1(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_54,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_57,plain,(
    ! [A_59] :
      ( u1_struct_0(A_59) = k2_struct_0(A_59)
      | ~ l1_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_65,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_57])).

tff(c_52,plain,(
    l1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_64,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_57])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_83,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_64,c_46])).

tff(c_88,plain,(
    ! [B_65,A_66] :
      ( v1_relat_1(B_65)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_66))
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_91,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_83,c_88])).

tff(c_97,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_91])).

tff(c_133,plain,(
    ! [C_77,A_78,B_79] :
      ( v4_relat_1(C_77,A_78)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_141,plain,(
    v4_relat_1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_83,c_133])).

tff(c_187,plain,(
    ! [B_96,A_97] :
      ( k1_relat_1(B_96) = A_97
      | ~ v1_partfun1(B_96,A_97)
      | ~ v4_relat_1(B_96,A_97)
      | ~ v1_relat_1(B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_190,plain,
    ( k2_struct_0('#skF_2') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',k2_struct_0('#skF_2'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_141,c_187])).

tff(c_193,plain,
    ( k2_struct_0('#skF_2') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_190])).

tff(c_195,plain,(
    ~ v1_partfun1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_193])).

tff(c_50,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_48,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_75,plain,(
    v1_funct_2('#skF_4',k2_struct_0('#skF_2'),k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_64,c_48])).

tff(c_275,plain,(
    ! [C_124,A_125,B_126] :
      ( v1_partfun1(C_124,A_125)
      | ~ v1_funct_2(C_124,A_125,B_126)
      | ~ v1_funct_1(C_124)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126)))
      | v1_xboole_0(B_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_278,plain,
    ( v1_partfun1('#skF_4',k2_struct_0('#skF_2'))
    | ~ v1_funct_2('#skF_4',k2_struct_0('#skF_2'),k2_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_83,c_275])).

tff(c_285,plain,
    ( v1_partfun1('#skF_4',k2_struct_0('#skF_2'))
    | v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_75,c_278])).

tff(c_286,plain,(
    v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_195,c_285])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_290,plain,(
    k2_struct_0('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_286,c_2])).

tff(c_294,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_290])).

tff(c_295,plain,(
    k2_struct_0('#skF_2') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_193])).

tff(c_42,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k2_struct_0('#skF_3')) != k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_106,plain,(
    k8_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'),'#skF_4',k2_struct_0('#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_64,c_42])).

tff(c_300,plain,(
    k8_relset_1(k1_relat_1('#skF_4'),k2_struct_0('#skF_3'),'#skF_4',k2_struct_0('#skF_3')) != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_295,c_106])).

tff(c_302,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k2_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_83])).

tff(c_22,plain,(
    ! [A_17,B_18,C_19] :
      ( k1_relset_1(A_17,B_18,C_19) = k1_relat_1(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_377,plain,(
    k1_relset_1(k1_relat_1('#skF_4'),k2_struct_0('#skF_3'),'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_302,c_22])).

tff(c_420,plain,(
    ! [A_144,B_145,C_146] :
      ( k8_relset_1(A_144,B_145,C_146,B_145) = k1_relset_1(A_144,B_145,C_146)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(A_144,B_145))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_422,plain,(
    k8_relset_1(k1_relat_1('#skF_4'),k2_struct_0('#skF_3'),'#skF_4',k2_struct_0('#skF_3')) = k1_relset_1(k1_relat_1('#skF_4'),k2_struct_0('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_302,c_420])).

tff(c_427,plain,(
    k8_relset_1(k1_relat_1('#skF_4'),k2_struct_0('#skF_3'),'#skF_4',k2_struct_0('#skF_3')) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_377,c_422])).

tff(c_429,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_300,c_427])).

tff(c_431,plain,(
    k2_struct_0('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_437,plain,(
    u1_struct_0('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_431,c_64])).

tff(c_430,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_432,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_430,c_65])).

tff(c_475,plain,(
    k8_relset_1(k1_xboole_0,k1_xboole_0,'#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_437,c_432,c_431,c_430,c_42])).

tff(c_459,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_437,c_432,c_46])).

tff(c_464,plain,(
    ! [B_152,A_153] :
      ( v1_relat_1(B_152)
      | ~ m1_subset_1(B_152,k1_zfmisc_1(A_153))
      | ~ v1_relat_1(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_467,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_459,c_464])).

tff(c_473,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_467])).

tff(c_493,plain,(
    ! [C_160,A_161,B_162] :
      ( v4_relat_1(C_160,A_161)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(A_161,B_162))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_501,plain,(
    v4_relat_1('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_459,c_493])).

tff(c_557,plain,(
    ! [B_181,A_182] :
      ( k1_relat_1(B_181) = A_182
      | ~ v1_partfun1(B_181,A_182)
      | ~ v4_relat_1(B_181,A_182)
      | ~ v1_relat_1(B_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_560,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_partfun1('#skF_4',k1_xboole_0)
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_501,c_557])).

tff(c_563,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_partfun1('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_473,c_560])).

tff(c_564,plain,(
    ~ v1_partfun1('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_563])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k1_relat_1(B_11),A_10)
      | ~ v4_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_30,plain,(
    ! [A_23] :
      ( r2_hidden('#skF_1'(A_23),A_23)
      | k1_xboole_0 = A_23 ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(A_2,k1_zfmisc_1(B_3))
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_503,plain,(
    ! [C_163,B_164,A_165] :
      ( ~ v1_xboole_0(C_163)
      | ~ m1_subset_1(B_164,k1_zfmisc_1(C_163))
      | ~ r2_hidden(A_165,B_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_532,plain,(
    ! [B_172,A_173,A_174] :
      ( ~ v1_xboole_0(B_172)
      | ~ r2_hidden(A_173,A_174)
      | ~ r1_tarski(A_174,B_172) ) ),
    inference(resolution,[status(thm)],[c_6,c_503])).

tff(c_536,plain,(
    ! [B_175,A_176] :
      ( ~ v1_xboole_0(B_175)
      | ~ r1_tarski(A_176,B_175)
      | k1_xboole_0 = A_176 ) ),
    inference(resolution,[status(thm)],[c_30,c_532])).

tff(c_572,plain,(
    ! [A_185,B_186] :
      ( ~ v1_xboole_0(A_185)
      | k1_relat_1(B_186) = k1_xboole_0
      | ~ v4_relat_1(B_186,A_185)
      | ~ v1_relat_1(B_186) ) ),
    inference(resolution,[status(thm)],[c_14,c_536])).

tff(c_575,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_501,c_572])).

tff(c_578,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_473,c_575])).

tff(c_579,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_578])).

tff(c_446,plain,(
    v1_funct_2('#skF_4',k1_xboole_0,u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_432,c_48])).

tff(c_447,plain,(
    v1_funct_2('#skF_4',k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_437,c_446])).

tff(c_642,plain,(
    ! [C_208,A_209,B_210] :
      ( v1_partfun1(C_208,A_209)
      | ~ v1_funct_2(C_208,A_209,B_210)
      | ~ v1_funct_1(C_208)
      | ~ m1_subset_1(C_208,k1_zfmisc_1(k2_zfmisc_1(A_209,B_210)))
      | v1_xboole_0(B_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_645,plain,
    ( v1_partfun1('#skF_4',k1_xboole_0)
    | ~ v1_funct_2('#skF_4',k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_459,c_642])).

tff(c_652,plain,
    ( v1_partfun1('#skF_4',k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_447,c_645])).

tff(c_654,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_579,c_564,c_652])).

tff(c_655,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_578])).

tff(c_36,plain,(
    ! [B_50] :
      ( v1_partfun1(B_50,k1_relat_1(B_50))
      | ~ v4_relat_1(B_50,k1_relat_1(B_50))
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_665,plain,
    ( v1_partfun1('#skF_4',k1_relat_1('#skF_4'))
    | ~ v4_relat_1('#skF_4',k1_xboole_0)
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_655,c_36])).

tff(c_675,plain,(
    v1_partfun1('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_473,c_501,c_655,c_665])).

tff(c_677,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_564,c_675])).

tff(c_678,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_563])).

tff(c_739,plain,(
    ! [A_214,B_215,C_216] :
      ( k1_relset_1(A_214,B_215,C_216) = k1_relat_1(C_216)
      | ~ m1_subset_1(C_216,k1_zfmisc_1(k2_zfmisc_1(A_214,B_215))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_742,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_459,c_739])).

tff(c_748,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_678,c_742])).

tff(c_778,plain,(
    ! [A_221,B_222,C_223] :
      ( k8_relset_1(A_221,B_222,C_223,B_222) = k1_relset_1(A_221,B_222,C_223)
      | ~ m1_subset_1(C_223,k1_zfmisc_1(k2_zfmisc_1(A_221,B_222))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_780,plain,(
    k8_relset_1(k1_xboole_0,k1_xboole_0,'#skF_4',k1_xboole_0) = k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_4') ),
    inference(resolution,[status(thm)],[c_459,c_778])).

tff(c_785,plain,(
    k8_relset_1(k1_xboole_0,k1_xboole_0,'#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_748,c_780])).

tff(c_787,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_475,c_785])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:50:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.74/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.39  
% 2.74/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.39  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.06/1.39  
% 3.06/1.39  %Foreground sorts:
% 3.06/1.39  
% 3.06/1.39  
% 3.06/1.39  %Background operators:
% 3.06/1.39  
% 3.06/1.39  
% 3.06/1.39  %Foreground operators:
% 3.06/1.39  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.06/1.39  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.06/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.06/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.06/1.39  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.06/1.39  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.06/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.06/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.06/1.39  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.06/1.39  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.06/1.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.06/1.39  tff('#skF_2', type, '#skF_2': $i).
% 3.06/1.39  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.06/1.39  tff('#skF_3', type, '#skF_3': $i).
% 3.06/1.39  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.06/1.39  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.06/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.06/1.39  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.06/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.06/1.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.06/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.06/1.39  tff('#skF_4', type, '#skF_4': $i).
% 3.06/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.06/1.39  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.06/1.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.06/1.39  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.06/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.06/1.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.06/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.06/1.39  
% 3.06/1.41  tff(f_137, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_struct_0(B) = k1_xboole_0) => (k2_struct_0(A) = k1_xboole_0)) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k2_struct_0(B)) = k2_struct_0(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_tops_2)).
% 3.06/1.41  tff(f_55, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.06/1.41  tff(f_118, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.06/1.41  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.06/1.41  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.06/1.41  tff(f_114, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 3.06/1.41  tff(f_106, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.06/1.41  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.06/1.41  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.06/1.41  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 3.06/1.41  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.06/1.41  tff(f_92, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_mcart_1)).
% 3.06/1.41  tff(f_33, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.06/1.41  tff(f_40, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.06/1.41  tff(c_44, plain, (k2_struct_0('#skF_2')=k1_xboole_0 | k2_struct_0('#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.06/1.41  tff(c_74, plain, (k2_struct_0('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_44])).
% 3.06/1.41  tff(c_16, plain, (![A_12, B_13]: (v1_relat_1(k2_zfmisc_1(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.06/1.41  tff(c_54, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.06/1.41  tff(c_57, plain, (![A_59]: (u1_struct_0(A_59)=k2_struct_0(A_59) | ~l1_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.06/1.41  tff(c_65, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_57])).
% 3.06/1.41  tff(c_52, plain, (l1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.06/1.41  tff(c_64, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_52, c_57])).
% 3.06/1.41  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.06/1.41  tff(c_83, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_64, c_46])).
% 3.06/1.41  tff(c_88, plain, (![B_65, A_66]: (v1_relat_1(B_65) | ~m1_subset_1(B_65, k1_zfmisc_1(A_66)) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.06/1.41  tff(c_91, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_83, c_88])).
% 3.06/1.41  tff(c_97, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_91])).
% 3.06/1.41  tff(c_133, plain, (![C_77, A_78, B_79]: (v4_relat_1(C_77, A_78) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.06/1.41  tff(c_141, plain, (v4_relat_1('#skF_4', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_83, c_133])).
% 3.06/1.41  tff(c_187, plain, (![B_96, A_97]: (k1_relat_1(B_96)=A_97 | ~v1_partfun1(B_96, A_97) | ~v4_relat_1(B_96, A_97) | ~v1_relat_1(B_96))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.06/1.41  tff(c_190, plain, (k2_struct_0('#skF_2')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', k2_struct_0('#skF_2')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_141, c_187])).
% 3.06/1.41  tff(c_193, plain, (k2_struct_0('#skF_2')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_190])).
% 3.06/1.41  tff(c_195, plain, (~v1_partfun1('#skF_4', k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_193])).
% 3.06/1.41  tff(c_50, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.06/1.41  tff(c_48, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.06/1.41  tff(c_75, plain, (v1_funct_2('#skF_4', k2_struct_0('#skF_2'), k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_64, c_48])).
% 3.06/1.41  tff(c_275, plain, (![C_124, A_125, B_126]: (v1_partfun1(C_124, A_125) | ~v1_funct_2(C_124, A_125, B_126) | ~v1_funct_1(C_124) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))) | v1_xboole_0(B_126))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.06/1.41  tff(c_278, plain, (v1_partfun1('#skF_4', k2_struct_0('#skF_2')) | ~v1_funct_2('#skF_4', k2_struct_0('#skF_2'), k2_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | v1_xboole_0(k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_83, c_275])).
% 3.06/1.41  tff(c_285, plain, (v1_partfun1('#skF_4', k2_struct_0('#skF_2')) | v1_xboole_0(k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_75, c_278])).
% 3.06/1.41  tff(c_286, plain, (v1_xboole_0(k2_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_195, c_285])).
% 3.06/1.41  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.06/1.41  tff(c_290, plain, (k2_struct_0('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_286, c_2])).
% 3.06/1.41  tff(c_294, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_290])).
% 3.06/1.41  tff(c_295, plain, (k2_struct_0('#skF_2')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_193])).
% 3.06/1.41  tff(c_42, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k2_struct_0('#skF_3'))!=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.06/1.41  tff(c_106, plain, (k8_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'), '#skF_4', k2_struct_0('#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_64, c_42])).
% 3.06/1.41  tff(c_300, plain, (k8_relset_1(k1_relat_1('#skF_4'), k2_struct_0('#skF_3'), '#skF_4', k2_struct_0('#skF_3'))!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_295, c_295, c_106])).
% 3.06/1.41  tff(c_302, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_295, c_83])).
% 3.06/1.41  tff(c_22, plain, (![A_17, B_18, C_19]: (k1_relset_1(A_17, B_18, C_19)=k1_relat_1(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.06/1.41  tff(c_377, plain, (k1_relset_1(k1_relat_1('#skF_4'), k2_struct_0('#skF_3'), '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_302, c_22])).
% 3.06/1.41  tff(c_420, plain, (![A_144, B_145, C_146]: (k8_relset_1(A_144, B_145, C_146, B_145)=k1_relset_1(A_144, B_145, C_146) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.06/1.41  tff(c_422, plain, (k8_relset_1(k1_relat_1('#skF_4'), k2_struct_0('#skF_3'), '#skF_4', k2_struct_0('#skF_3'))=k1_relset_1(k1_relat_1('#skF_4'), k2_struct_0('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_302, c_420])).
% 3.06/1.41  tff(c_427, plain, (k8_relset_1(k1_relat_1('#skF_4'), k2_struct_0('#skF_3'), '#skF_4', k2_struct_0('#skF_3'))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_377, c_422])).
% 3.06/1.41  tff(c_429, plain, $false, inference(negUnitSimplification, [status(thm)], [c_300, c_427])).
% 3.06/1.41  tff(c_431, plain, (k2_struct_0('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_44])).
% 3.06/1.41  tff(c_437, plain, (u1_struct_0('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_431, c_64])).
% 3.06/1.41  tff(c_430, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_44])).
% 3.06/1.41  tff(c_432, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_430, c_65])).
% 3.06/1.41  tff(c_475, plain, (k8_relset_1(k1_xboole_0, k1_xboole_0, '#skF_4', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_437, c_432, c_431, c_430, c_42])).
% 3.06/1.41  tff(c_459, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_437, c_432, c_46])).
% 3.06/1.41  tff(c_464, plain, (![B_152, A_153]: (v1_relat_1(B_152) | ~m1_subset_1(B_152, k1_zfmisc_1(A_153)) | ~v1_relat_1(A_153))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.06/1.41  tff(c_467, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0))), inference(resolution, [status(thm)], [c_459, c_464])).
% 3.06/1.41  tff(c_473, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_467])).
% 3.06/1.41  tff(c_493, plain, (![C_160, A_161, B_162]: (v4_relat_1(C_160, A_161) | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(A_161, B_162))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.06/1.41  tff(c_501, plain, (v4_relat_1('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_459, c_493])).
% 3.06/1.41  tff(c_557, plain, (![B_181, A_182]: (k1_relat_1(B_181)=A_182 | ~v1_partfun1(B_181, A_182) | ~v4_relat_1(B_181, A_182) | ~v1_relat_1(B_181))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.06/1.41  tff(c_560, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_partfun1('#skF_4', k1_xboole_0) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_501, c_557])).
% 3.06/1.41  tff(c_563, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_partfun1('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_473, c_560])).
% 3.06/1.41  tff(c_564, plain, (~v1_partfun1('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_563])).
% 3.06/1.41  tff(c_14, plain, (![B_11, A_10]: (r1_tarski(k1_relat_1(B_11), A_10) | ~v4_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.06/1.41  tff(c_30, plain, (![A_23]: (r2_hidden('#skF_1'(A_23), A_23) | k1_xboole_0=A_23)), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.06/1.41  tff(c_6, plain, (![A_2, B_3]: (m1_subset_1(A_2, k1_zfmisc_1(B_3)) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.06/1.41  tff(c_503, plain, (![C_163, B_164, A_165]: (~v1_xboole_0(C_163) | ~m1_subset_1(B_164, k1_zfmisc_1(C_163)) | ~r2_hidden(A_165, B_164))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.06/1.41  tff(c_532, plain, (![B_172, A_173, A_174]: (~v1_xboole_0(B_172) | ~r2_hidden(A_173, A_174) | ~r1_tarski(A_174, B_172))), inference(resolution, [status(thm)], [c_6, c_503])).
% 3.06/1.41  tff(c_536, plain, (![B_175, A_176]: (~v1_xboole_0(B_175) | ~r1_tarski(A_176, B_175) | k1_xboole_0=A_176)), inference(resolution, [status(thm)], [c_30, c_532])).
% 3.06/1.41  tff(c_572, plain, (![A_185, B_186]: (~v1_xboole_0(A_185) | k1_relat_1(B_186)=k1_xboole_0 | ~v4_relat_1(B_186, A_185) | ~v1_relat_1(B_186))), inference(resolution, [status(thm)], [c_14, c_536])).
% 3.06/1.41  tff(c_575, plain, (~v1_xboole_0(k1_xboole_0) | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_501, c_572])).
% 3.06/1.41  tff(c_578, plain, (~v1_xboole_0(k1_xboole_0) | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_473, c_575])).
% 3.06/1.41  tff(c_579, plain, (~v1_xboole_0(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_578])).
% 3.06/1.41  tff(c_446, plain, (v1_funct_2('#skF_4', k1_xboole_0, u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_432, c_48])).
% 3.06/1.41  tff(c_447, plain, (v1_funct_2('#skF_4', k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_437, c_446])).
% 3.06/1.41  tff(c_642, plain, (![C_208, A_209, B_210]: (v1_partfun1(C_208, A_209) | ~v1_funct_2(C_208, A_209, B_210) | ~v1_funct_1(C_208) | ~m1_subset_1(C_208, k1_zfmisc_1(k2_zfmisc_1(A_209, B_210))) | v1_xboole_0(B_210))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.06/1.41  tff(c_645, plain, (v1_partfun1('#skF_4', k1_xboole_0) | ~v1_funct_2('#skF_4', k1_xboole_0, k1_xboole_0) | ~v1_funct_1('#skF_4') | v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_459, c_642])).
% 3.06/1.41  tff(c_652, plain, (v1_partfun1('#skF_4', k1_xboole_0) | v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_447, c_645])).
% 3.06/1.41  tff(c_654, plain, $false, inference(negUnitSimplification, [status(thm)], [c_579, c_564, c_652])).
% 3.06/1.41  tff(c_655, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_578])).
% 3.06/1.41  tff(c_36, plain, (![B_50]: (v1_partfun1(B_50, k1_relat_1(B_50)) | ~v4_relat_1(B_50, k1_relat_1(B_50)) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.06/1.41  tff(c_665, plain, (v1_partfun1('#skF_4', k1_relat_1('#skF_4')) | ~v4_relat_1('#skF_4', k1_xboole_0) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_655, c_36])).
% 3.06/1.41  tff(c_675, plain, (v1_partfun1('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_473, c_501, c_655, c_665])).
% 3.06/1.41  tff(c_677, plain, $false, inference(negUnitSimplification, [status(thm)], [c_564, c_675])).
% 3.06/1.41  tff(c_678, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_563])).
% 3.06/1.41  tff(c_739, plain, (![A_214, B_215, C_216]: (k1_relset_1(A_214, B_215, C_216)=k1_relat_1(C_216) | ~m1_subset_1(C_216, k1_zfmisc_1(k2_zfmisc_1(A_214, B_215))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.06/1.41  tff(c_742, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_459, c_739])).
% 3.06/1.41  tff(c_748, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_678, c_742])).
% 3.06/1.41  tff(c_778, plain, (![A_221, B_222, C_223]: (k8_relset_1(A_221, B_222, C_223, B_222)=k1_relset_1(A_221, B_222, C_223) | ~m1_subset_1(C_223, k1_zfmisc_1(k2_zfmisc_1(A_221, B_222))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.06/1.41  tff(c_780, plain, (k8_relset_1(k1_xboole_0, k1_xboole_0, '#skF_4', k1_xboole_0)=k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_4')), inference(resolution, [status(thm)], [c_459, c_778])).
% 3.06/1.41  tff(c_785, plain, (k8_relset_1(k1_xboole_0, k1_xboole_0, '#skF_4', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_748, c_780])).
% 3.06/1.41  tff(c_787, plain, $false, inference(negUnitSimplification, [status(thm)], [c_475, c_785])).
% 3.06/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.41  
% 3.06/1.41  Inference rules
% 3.06/1.41  ----------------------
% 3.06/1.41  #Ref     : 0
% 3.06/1.41  #Sup     : 154
% 3.06/1.41  #Fact    : 0
% 3.06/1.41  #Define  : 0
% 3.06/1.41  #Split   : 9
% 3.06/1.41  #Chain   : 0
% 3.06/1.41  #Close   : 0
% 3.06/1.41  
% 3.06/1.41  Ordering : KBO
% 3.06/1.41  
% 3.06/1.41  Simplification rules
% 3.06/1.41  ----------------------
% 3.06/1.41  #Subsume      : 8
% 3.06/1.41  #Demod        : 99
% 3.06/1.41  #Tautology    : 70
% 3.06/1.41  #SimpNegUnit  : 7
% 3.06/1.41  #BackRed      : 13
% 3.06/1.41  
% 3.06/1.41  #Partial instantiations: 0
% 3.06/1.41  #Strategies tried      : 1
% 3.06/1.41  
% 3.06/1.41  Timing (in seconds)
% 3.06/1.41  ----------------------
% 3.06/1.41  Preprocessing        : 0.33
% 3.06/1.41  Parsing              : 0.18
% 3.06/1.41  CNF conversion       : 0.02
% 3.06/1.41  Main loop            : 0.32
% 3.06/1.41  Inferencing          : 0.12
% 3.06/1.41  Reduction            : 0.10
% 3.06/1.41  Demodulation         : 0.07
% 3.06/1.41  BG Simplification    : 0.02
% 3.06/1.41  Subsumption          : 0.04
% 3.06/1.41  Abstraction          : 0.02
% 3.06/1.41  MUC search           : 0.00
% 3.06/1.41  Cooper               : 0.00
% 3.06/1.41  Total                : 0.69
% 3.06/1.41  Index Insertion      : 0.00
% 3.06/1.41  Index Deletion       : 0.00
% 3.06/1.41  Index Matching       : 0.00
% 3.06/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
