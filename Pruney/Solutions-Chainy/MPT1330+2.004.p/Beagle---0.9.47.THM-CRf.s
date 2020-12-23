%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:09 EST 2020

% Result     : Theorem 3.90s
% Output     : CNFRefutation 4.16s
% Verified   : 
% Statistics : Number of formulae       :  159 (1073 expanded)
%              Number of leaves         :   53 ( 390 expanded)
%              Depth                    :   15
%              Number of atoms          :  230 (2231 expanded)
%              Number of equality atoms :   90 ( 982 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k6_relat_1 > k2_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(f_93,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_59,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_181,negated_conjecture,(
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

tff(f_162,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_141,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_158,axiom,(
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

tff(f_112,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_86,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v1_xboole_0(A)
        & v1_relat_1(A) )
     => ( v1_xboole_0(k7_relat_1(A,B))
        & v1_relat_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc17_relat_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_82,axiom,(
    ! [A,B] : r1_tarski(k2_relat_1(k2_zfmisc_1(A,B)),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t194_relat_1)).

tff(c_40,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_84,plain,(
    ! [A_69] : v1_relat_1(k6_relat_1(A_69)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_86,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_84])).

tff(c_8,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_26,plain,(
    ! [A_14,B_15] : v1_relat_1(k2_zfmisc_1(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_78,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_177,plain,(
    ! [A_85] :
      ( u1_struct_0(A_85) = k2_struct_0(A_85)
      | ~ l1_struct_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_185,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_177])).

tff(c_76,plain,(
    l1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_184,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_177])).

tff(c_70,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_207,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_184,c_70])).

tff(c_222,plain,(
    ! [B_92,A_93] :
      ( v1_relat_1(B_92)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(A_93))
      | ~ v1_relat_1(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_225,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_207,c_222])).

tff(c_228,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_225])).

tff(c_305,plain,(
    ! [C_108,A_109,B_110] :
      ( v4_relat_1(C_108,A_109)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_315,plain,(
    v4_relat_1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_207,c_305])).

tff(c_402,plain,(
    ! [B_127,A_128] :
      ( k1_relat_1(B_127) = A_128
      | ~ v1_partfun1(B_127,A_128)
      | ~ v4_relat_1(B_127,A_128)
      | ~ v1_relat_1(B_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_405,plain,
    ( k2_struct_0('#skF_2') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',k2_struct_0('#skF_2'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_315,c_402])).

tff(c_408,plain,
    ( k2_struct_0('#skF_2') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_405])).

tff(c_415,plain,(
    ~ v1_partfun1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_408])).

tff(c_68,plain,
    ( k2_struct_0('#skF_2') = k1_xboole_0
    | k2_struct_0('#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_94,plain,(
    k2_struct_0('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_74,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_72,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_191,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_72])).

tff(c_208,plain,(
    v1_funct_2('#skF_4',k2_struct_0('#skF_2'),k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_191])).

tff(c_793,plain,(
    ! [B_160,C_161,A_162] :
      ( k1_xboole_0 = B_160
      | v1_partfun1(C_161,A_162)
      | ~ v1_funct_2(C_161,A_162,B_160)
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(A_162,B_160)))
      | ~ v1_funct_1(C_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_796,plain,
    ( k2_struct_0('#skF_3') = k1_xboole_0
    | v1_partfun1('#skF_4',k2_struct_0('#skF_2'))
    | ~ v1_funct_2('#skF_4',k2_struct_0('#skF_2'),k2_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_207,c_793])).

tff(c_805,plain,
    ( k2_struct_0('#skF_3') = k1_xboole_0
    | v1_partfun1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_208,c_796])).

tff(c_807,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_415,c_94,c_805])).

tff(c_808,plain,(
    k2_struct_0('#skF_2') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_408])).

tff(c_814,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k2_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_808,c_207])).

tff(c_1094,plain,(
    ! [A_181,B_182,C_183,D_184] :
      ( k8_relset_1(A_181,B_182,C_183,D_184) = k10_relat_1(C_183,D_184)
      | ~ m1_subset_1(C_183,k1_zfmisc_1(k2_zfmisc_1(A_181,B_182))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1101,plain,(
    ! [D_184] : k8_relset_1(k1_relat_1('#skF_4'),k2_struct_0('#skF_3'),'#skF_4',D_184) = k10_relat_1('#skF_4',D_184) ),
    inference(resolution,[status(thm)],[c_814,c_1094])).

tff(c_66,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k2_struct_0('#skF_3')) != k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_266,plain,(
    k8_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'),'#skF_4',k2_struct_0('#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_184,c_66])).

tff(c_812,plain,(
    k8_relset_1(k1_relat_1('#skF_4'),k2_struct_0('#skF_3'),'#skF_4',k2_struct_0('#skF_3')) != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_808,c_808,c_266])).

tff(c_1309,plain,(
    k10_relat_1('#skF_4',k2_struct_0('#skF_3')) != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1101,c_812])).

tff(c_321,plain,(
    ! [C_113,B_114,A_115] :
      ( v5_relat_1(C_113,B_114)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_115,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_331,plain,(
    v5_relat_1('#skF_4',k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_207,c_321])).

tff(c_18,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k2_relat_1(B_10),A_9)
      | ~ v5_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_863,plain,(
    ! [B_163,A_164] :
      ( k5_relat_1(B_163,k6_relat_1(A_164)) = B_163
      | ~ r1_tarski(k2_relat_1(B_163),A_164)
      | ~ v1_relat_1(B_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_879,plain,(
    ! [B_10,A_9] :
      ( k5_relat_1(B_10,k6_relat_1(A_9)) = B_10
      | ~ v5_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(resolution,[status(thm)],[c_18,c_863])).

tff(c_20,plain,(
    ! [A_11] : v1_relat_1(k6_relat_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_34,plain,(
    ! [A_23] : k1_relat_1(k6_relat_1(A_23)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1032,plain,(
    ! [A_177,B_178] :
      ( k10_relat_1(A_177,k1_relat_1(B_178)) = k1_relat_1(k5_relat_1(A_177,B_178))
      | ~ v1_relat_1(B_178)
      | ~ v1_relat_1(A_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1044,plain,(
    ! [A_177,A_23] :
      ( k1_relat_1(k5_relat_1(A_177,k6_relat_1(A_23))) = k10_relat_1(A_177,A_23)
      | ~ v1_relat_1(k6_relat_1(A_23))
      | ~ v1_relat_1(A_177) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1032])).

tff(c_1102,plain,(
    ! [A_185,A_186] :
      ( k1_relat_1(k5_relat_1(A_185,k6_relat_1(A_186))) = k10_relat_1(A_185,A_186)
      | ~ v1_relat_1(A_185) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1044])).

tff(c_1321,plain,(
    ! [B_204,A_205] :
      ( k10_relat_1(B_204,A_205) = k1_relat_1(B_204)
      | ~ v1_relat_1(B_204)
      | ~ v5_relat_1(B_204,A_205)
      | ~ v1_relat_1(B_204) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_879,c_1102])).

tff(c_1324,plain,
    ( k10_relat_1('#skF_4',k2_struct_0('#skF_3')) = k1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_331,c_1321])).

tff(c_1336,plain,(
    k10_relat_1('#skF_4',k2_struct_0('#skF_3')) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_1324])).

tff(c_1338,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1309,c_1336])).

tff(c_1340,plain,(
    k2_struct_0('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_1409,plain,(
    ! [A_210] :
      ( u1_struct_0(A_210) = k2_struct_0(A_210)
      | ~ l1_struct_0(A_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_1412,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_1409])).

tff(c_1417,plain,(
    u1_struct_0('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1340,c_1412])).

tff(c_1440,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1417,c_70])).

tff(c_1477,plain,(
    ! [B_223,A_224] :
      ( v1_relat_1(B_223)
      | ~ m1_subset_1(B_223,k1_zfmisc_1(A_224))
      | ~ v1_relat_1(A_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1480,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1440,c_1477])).

tff(c_1483,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1480])).

tff(c_1349,plain,(
    ! [A_206] : k2_relat_1(k6_relat_1(A_206)) = A_206 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1358,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_1349])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1458,plain,(
    ! [A_220,B_221] :
      ( v1_xboole_0(k7_relat_1(A_220,B_221))
      | ~ v1_relat_1(A_220)
      | ~ v1_xboole_0(A_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1448,plain,(
    ! [B_217,A_218] :
      ( ~ v1_xboole_0(B_217)
      | B_217 = A_218
      | ~ v1_xboole_0(A_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1451,plain,(
    ! [A_218] :
      ( k1_xboole_0 = A_218
      | ~ v1_xboole_0(A_218) ) ),
    inference(resolution,[status(thm)],[c_2,c_1448])).

tff(c_1497,plain,(
    ! [A_229,B_230] :
      ( k7_relat_1(A_229,B_230) = k1_xboole_0
      | ~ v1_relat_1(A_229)
      | ~ v1_xboole_0(A_229) ) ),
    inference(resolution,[status(thm)],[c_1458,c_1451])).

tff(c_1501,plain,(
    ! [B_230] :
      ( k7_relat_1(k1_xboole_0,B_230) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2,c_1497])).

tff(c_1505,plain,(
    ! [B_230] : k7_relat_1(k1_xboole_0,B_230) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1501])).

tff(c_1625,plain,(
    ! [B_258,A_259] :
      ( k2_relat_1(k7_relat_1(B_258,A_259)) = k9_relat_1(B_258,A_259)
      | ~ v1_relat_1(B_258) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1640,plain,(
    ! [B_230] :
      ( k9_relat_1(k1_xboole_0,B_230) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1505,c_1625])).

tff(c_1645,plain,(
    ! [B_260] : k9_relat_1(k1_xboole_0,B_260) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1358,c_1640])).

tff(c_1615,plain,(
    ! [A_256,B_257] :
      ( k9_relat_1(k6_relat_1(A_256),B_257) = B_257
      | ~ m1_subset_1(B_257,k1_zfmisc_1(A_256)) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1618,plain,(
    k9_relat_1(k6_relat_1(k1_xboole_0),'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1440,c_1615])).

tff(c_1620,plain,(
    k9_relat_1(k1_xboole_0,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1618])).

tff(c_1649,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1645,c_1620])).

tff(c_1393,plain,(
    ! [A_209] : k1_relat_1(k6_relat_1(A_209)) = A_209 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1402,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_1393])).

tff(c_1673,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1649,c_1649,c_1402])).

tff(c_10,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1431,plain,(
    ! [A_213,B_214] : r1_tarski(k2_relat_1(k2_zfmisc_1(A_213,B_214)),B_214) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1434,plain,(
    ! [B_4] : r1_tarski(k2_relat_1(k1_xboole_0),B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1431])).

tff(c_1438,plain,(
    ! [B_4] : r1_tarski(k1_xboole_0,B_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1358,c_1434])).

tff(c_1668,plain,(
    ! [B_4] : r1_tarski('#skF_4',B_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1649,c_1438])).

tff(c_1676,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1649,c_1649,c_1358])).

tff(c_1750,plain,(
    ! [B_263,A_264] :
      ( k5_relat_1(B_263,k6_relat_1(A_264)) = B_263
      | ~ r1_tarski(k2_relat_1(B_263),A_264)
      | ~ v1_relat_1(B_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1753,plain,(
    ! [A_264] :
      ( k5_relat_1('#skF_4',k6_relat_1(A_264)) = '#skF_4'
      | ~ r1_tarski('#skF_4',A_264)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1676,c_1750])).

tff(c_1767,plain,(
    ! [A_264] : k5_relat_1('#skF_4',k6_relat_1(A_264)) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1483,c_1668,c_1753])).

tff(c_1939,plain,(
    ! [A_275,B_276] :
      ( k10_relat_1(A_275,k1_relat_1(B_276)) = k1_relat_1(k5_relat_1(A_275,B_276))
      | ~ v1_relat_1(B_276)
      | ~ v1_relat_1(A_275) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1951,plain,(
    ! [A_275,A_23] :
      ( k1_relat_1(k5_relat_1(A_275,k6_relat_1(A_23))) = k10_relat_1(A_275,A_23)
      | ~ v1_relat_1(k6_relat_1(A_23))
      | ~ v1_relat_1(A_275) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1939])).

tff(c_2072,plain,(
    ! [A_299,A_300] :
      ( k1_relat_1(k5_relat_1(A_299,k6_relat_1(A_300))) = k10_relat_1(A_299,A_300)
      | ~ v1_relat_1(A_299) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1951])).

tff(c_2090,plain,(
    ! [A_264] :
      ( k10_relat_1('#skF_4',A_264) = k1_relat_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1767,c_2072])).

tff(c_2099,plain,(
    ! [A_264] : k10_relat_1('#skF_4',A_264) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1483,c_1673,c_2090])).

tff(c_1669,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1649,c_1440])).

tff(c_1674,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_4',B_4) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1649,c_1649,c_10])).

tff(c_1975,plain,(
    ! [A_280,B_281,C_282,D_283] :
      ( k8_relset_1(A_280,B_281,C_282,D_283) = k10_relat_1(C_282,D_283)
      | ~ m1_subset_1(C_282,k1_zfmisc_1(k2_zfmisc_1(A_280,B_281))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_2494,plain,(
    ! [B_329,C_330,D_331] :
      ( k8_relset_1('#skF_4',B_329,C_330,D_331) = k10_relat_1(C_330,D_331)
      | ~ m1_subset_1(C_330,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1674,c_1975])).

tff(c_2496,plain,(
    ! [B_329,D_331] : k8_relset_1('#skF_4',B_329,'#skF_4',D_331) = k10_relat_1('#skF_4',D_331) ),
    inference(resolution,[status(thm)],[c_1669,c_2494])).

tff(c_2498,plain,(
    ! [B_329,D_331] : k8_relset_1('#skF_4',B_329,'#skF_4',D_331) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2099,c_2496])).

tff(c_1339,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_1415,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_1409])).

tff(c_1419,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1339,c_1415])).

tff(c_1484,plain,(
    k8_relset_1(k1_xboole_0,k1_xboole_0,'#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1419,c_1417,c_1340,c_1339,c_66])).

tff(c_1664,plain,(
    k8_relset_1('#skF_4','#skF_4','#skF_4','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1649,c_1649,c_1649,c_1649,c_1484])).

tff(c_2501,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2498,c_1664])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:16:44 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.90/1.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.16/1.68  
% 4.16/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.16/1.68  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k6_relat_1 > k2_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 4.16/1.68  
% 4.16/1.68  %Foreground sorts:
% 4.16/1.68  
% 4.16/1.68  
% 4.16/1.68  %Background operators:
% 4.16/1.68  
% 4.16/1.68  
% 4.16/1.68  %Foreground operators:
% 4.16/1.68  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.16/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.16/1.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.16/1.68  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.16/1.68  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 4.16/1.68  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.16/1.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.16/1.68  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.16/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.16/1.68  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.16/1.68  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.16/1.68  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.16/1.68  tff('#skF_2', type, '#skF_2': $i).
% 4.16/1.68  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.16/1.68  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.16/1.68  tff('#skF_3', type, '#skF_3': $i).
% 4.16/1.68  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.16/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.16/1.68  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.16/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.16/1.68  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.16/1.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.16/1.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.16/1.68  tff('#skF_4', type, '#skF_4': $i).
% 4.16/1.68  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.16/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.16/1.68  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.16/1.68  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.16/1.68  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.16/1.68  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.16/1.68  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.16/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.16/1.68  
% 4.16/1.71  tff(f_93, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 4.16/1.71  tff(f_59, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 4.16/1.71  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.16/1.71  tff(f_69, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.16/1.71  tff(f_181, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_struct_0(B) = k1_xboole_0) => (k2_struct_0(A) = k1_xboole_0)) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k2_struct_0(B)) = k2_struct_0(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_tops_2)).
% 4.16/1.71  tff(f_162, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 4.16/1.71  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.16/1.71  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.16/1.71  tff(f_141, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 4.16/1.71  tff(f_158, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_funct_2)).
% 4.16/1.71  tff(f_112, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 4.16/1.71  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 4.16/1.71  tff(f_92, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 4.16/1.71  tff(f_86, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 4.16/1.71  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 4.16/1.71  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.16/1.71  tff(f_67, axiom, (![A, B]: ((v1_xboole_0(A) & v1_relat_1(A)) => (v1_xboole_0(k7_relat_1(A, B)) & v1_relat_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc17_relat_1)).
% 4.16/1.71  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 4.16/1.71  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 4.16/1.71  tff(f_97, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_funct_1)).
% 4.16/1.71  tff(f_82, axiom, (![A, B]: r1_tarski(k2_relat_1(k2_zfmisc_1(A, B)), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t194_relat_1)).
% 4.16/1.71  tff(c_40, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.16/1.71  tff(c_84, plain, (![A_69]: (v1_relat_1(k6_relat_1(A_69)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.16/1.71  tff(c_86, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_40, c_84])).
% 4.16/1.71  tff(c_8, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.16/1.71  tff(c_26, plain, (![A_14, B_15]: (v1_relat_1(k2_zfmisc_1(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.16/1.71  tff(c_78, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_181])).
% 4.16/1.71  tff(c_177, plain, (![A_85]: (u1_struct_0(A_85)=k2_struct_0(A_85) | ~l1_struct_0(A_85))), inference(cnfTransformation, [status(thm)], [f_162])).
% 4.16/1.71  tff(c_185, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_78, c_177])).
% 4.16/1.71  tff(c_76, plain, (l1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_181])).
% 4.16/1.71  tff(c_184, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_76, c_177])).
% 4.16/1.71  tff(c_70, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_181])).
% 4.16/1.71  tff(c_207, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_185, c_184, c_70])).
% 4.16/1.71  tff(c_222, plain, (![B_92, A_93]: (v1_relat_1(B_92) | ~m1_subset_1(B_92, k1_zfmisc_1(A_93)) | ~v1_relat_1(A_93))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.16/1.71  tff(c_225, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_207, c_222])).
% 4.16/1.71  tff(c_228, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_225])).
% 4.16/1.71  tff(c_305, plain, (![C_108, A_109, B_110]: (v4_relat_1(C_108, A_109) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.16/1.71  tff(c_315, plain, (v4_relat_1('#skF_4', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_207, c_305])).
% 4.16/1.71  tff(c_402, plain, (![B_127, A_128]: (k1_relat_1(B_127)=A_128 | ~v1_partfun1(B_127, A_128) | ~v4_relat_1(B_127, A_128) | ~v1_relat_1(B_127))), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.16/1.71  tff(c_405, plain, (k2_struct_0('#skF_2')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', k2_struct_0('#skF_2')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_315, c_402])).
% 4.16/1.71  tff(c_408, plain, (k2_struct_0('#skF_2')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_228, c_405])).
% 4.16/1.71  tff(c_415, plain, (~v1_partfun1('#skF_4', k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_408])).
% 4.16/1.71  tff(c_68, plain, (k2_struct_0('#skF_2')=k1_xboole_0 | k2_struct_0('#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_181])).
% 4.16/1.71  tff(c_94, plain, (k2_struct_0('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_68])).
% 4.16/1.71  tff(c_74, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_181])).
% 4.16/1.71  tff(c_72, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_181])).
% 4.16/1.71  tff(c_191, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_184, c_72])).
% 4.16/1.71  tff(c_208, plain, (v1_funct_2('#skF_4', k2_struct_0('#skF_2'), k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_185, c_191])).
% 4.16/1.71  tff(c_793, plain, (![B_160, C_161, A_162]: (k1_xboole_0=B_160 | v1_partfun1(C_161, A_162) | ~v1_funct_2(C_161, A_162, B_160) | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(A_162, B_160))) | ~v1_funct_1(C_161))), inference(cnfTransformation, [status(thm)], [f_158])).
% 4.16/1.71  tff(c_796, plain, (k2_struct_0('#skF_3')=k1_xboole_0 | v1_partfun1('#skF_4', k2_struct_0('#skF_2')) | ~v1_funct_2('#skF_4', k2_struct_0('#skF_2'), k2_struct_0('#skF_3')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_207, c_793])).
% 4.16/1.71  tff(c_805, plain, (k2_struct_0('#skF_3')=k1_xboole_0 | v1_partfun1('#skF_4', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_208, c_796])).
% 4.16/1.71  tff(c_807, plain, $false, inference(negUnitSimplification, [status(thm)], [c_415, c_94, c_805])).
% 4.16/1.71  tff(c_808, plain, (k2_struct_0('#skF_2')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_408])).
% 4.16/1.71  tff(c_814, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_808, c_207])).
% 4.16/1.71  tff(c_1094, plain, (![A_181, B_182, C_183, D_184]: (k8_relset_1(A_181, B_182, C_183, D_184)=k10_relat_1(C_183, D_184) | ~m1_subset_1(C_183, k1_zfmisc_1(k2_zfmisc_1(A_181, B_182))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.16/1.71  tff(c_1101, plain, (![D_184]: (k8_relset_1(k1_relat_1('#skF_4'), k2_struct_0('#skF_3'), '#skF_4', D_184)=k10_relat_1('#skF_4', D_184))), inference(resolution, [status(thm)], [c_814, c_1094])).
% 4.16/1.71  tff(c_66, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k2_struct_0('#skF_3'))!=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_181])).
% 4.16/1.71  tff(c_266, plain, (k8_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'), '#skF_4', k2_struct_0('#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_185, c_184, c_66])).
% 4.16/1.71  tff(c_812, plain, (k8_relset_1(k1_relat_1('#skF_4'), k2_struct_0('#skF_3'), '#skF_4', k2_struct_0('#skF_3'))!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_808, c_808, c_266])).
% 4.16/1.71  tff(c_1309, plain, (k10_relat_1('#skF_4', k2_struct_0('#skF_3'))!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1101, c_812])).
% 4.16/1.71  tff(c_321, plain, (![C_113, B_114, A_115]: (v5_relat_1(C_113, B_114) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_115, B_114))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.16/1.71  tff(c_331, plain, (v5_relat_1('#skF_4', k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_207, c_321])).
% 4.16/1.71  tff(c_18, plain, (![B_10, A_9]: (r1_tarski(k2_relat_1(B_10), A_9) | ~v5_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.16/1.71  tff(c_863, plain, (![B_163, A_164]: (k5_relat_1(B_163, k6_relat_1(A_164))=B_163 | ~r1_tarski(k2_relat_1(B_163), A_164) | ~v1_relat_1(B_163))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.16/1.71  tff(c_879, plain, (![B_10, A_9]: (k5_relat_1(B_10, k6_relat_1(A_9))=B_10 | ~v5_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(resolution, [status(thm)], [c_18, c_863])).
% 4.16/1.71  tff(c_20, plain, (![A_11]: (v1_relat_1(k6_relat_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.16/1.71  tff(c_34, plain, (![A_23]: (k1_relat_1(k6_relat_1(A_23))=A_23)), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.16/1.71  tff(c_1032, plain, (![A_177, B_178]: (k10_relat_1(A_177, k1_relat_1(B_178))=k1_relat_1(k5_relat_1(A_177, B_178)) | ~v1_relat_1(B_178) | ~v1_relat_1(A_177))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.16/1.71  tff(c_1044, plain, (![A_177, A_23]: (k1_relat_1(k5_relat_1(A_177, k6_relat_1(A_23)))=k10_relat_1(A_177, A_23) | ~v1_relat_1(k6_relat_1(A_23)) | ~v1_relat_1(A_177))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1032])).
% 4.16/1.71  tff(c_1102, plain, (![A_185, A_186]: (k1_relat_1(k5_relat_1(A_185, k6_relat_1(A_186)))=k10_relat_1(A_185, A_186) | ~v1_relat_1(A_185))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1044])).
% 4.16/1.71  tff(c_1321, plain, (![B_204, A_205]: (k10_relat_1(B_204, A_205)=k1_relat_1(B_204) | ~v1_relat_1(B_204) | ~v5_relat_1(B_204, A_205) | ~v1_relat_1(B_204))), inference(superposition, [status(thm), theory('equality')], [c_879, c_1102])).
% 4.16/1.71  tff(c_1324, plain, (k10_relat_1('#skF_4', k2_struct_0('#skF_3'))=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_331, c_1321])).
% 4.16/1.71  tff(c_1336, plain, (k10_relat_1('#skF_4', k2_struct_0('#skF_3'))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_228, c_1324])).
% 4.16/1.71  tff(c_1338, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1309, c_1336])).
% 4.16/1.71  tff(c_1340, plain, (k2_struct_0('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_68])).
% 4.16/1.71  tff(c_1409, plain, (![A_210]: (u1_struct_0(A_210)=k2_struct_0(A_210) | ~l1_struct_0(A_210))), inference(cnfTransformation, [status(thm)], [f_162])).
% 4.16/1.71  tff(c_1412, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_76, c_1409])).
% 4.16/1.71  tff(c_1417, plain, (u1_struct_0('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1340, c_1412])).
% 4.16/1.71  tff(c_1440, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1417, c_70])).
% 4.16/1.71  tff(c_1477, plain, (![B_223, A_224]: (v1_relat_1(B_223) | ~m1_subset_1(B_223, k1_zfmisc_1(A_224)) | ~v1_relat_1(A_224))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.16/1.71  tff(c_1480, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_1440, c_1477])).
% 4.16/1.71  tff(c_1483, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1480])).
% 4.16/1.71  tff(c_1349, plain, (![A_206]: (k2_relat_1(k6_relat_1(A_206))=A_206)), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.16/1.71  tff(c_1358, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_40, c_1349])).
% 4.16/1.71  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.16/1.71  tff(c_1458, plain, (![A_220, B_221]: (v1_xboole_0(k7_relat_1(A_220, B_221)) | ~v1_relat_1(A_220) | ~v1_xboole_0(A_220))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.16/1.71  tff(c_1448, plain, (![B_217, A_218]: (~v1_xboole_0(B_217) | B_217=A_218 | ~v1_xboole_0(A_218))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.16/1.71  tff(c_1451, plain, (![A_218]: (k1_xboole_0=A_218 | ~v1_xboole_0(A_218))), inference(resolution, [status(thm)], [c_2, c_1448])).
% 4.16/1.71  tff(c_1497, plain, (![A_229, B_230]: (k7_relat_1(A_229, B_230)=k1_xboole_0 | ~v1_relat_1(A_229) | ~v1_xboole_0(A_229))), inference(resolution, [status(thm)], [c_1458, c_1451])).
% 4.16/1.71  tff(c_1501, plain, (![B_230]: (k7_relat_1(k1_xboole_0, B_230)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_1497])).
% 4.16/1.71  tff(c_1505, plain, (![B_230]: (k7_relat_1(k1_xboole_0, B_230)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1501])).
% 4.16/1.71  tff(c_1625, plain, (![B_258, A_259]: (k2_relat_1(k7_relat_1(B_258, A_259))=k9_relat_1(B_258, A_259) | ~v1_relat_1(B_258))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.16/1.71  tff(c_1640, plain, (![B_230]: (k9_relat_1(k1_xboole_0, B_230)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1505, c_1625])).
% 4.16/1.71  tff(c_1645, plain, (![B_260]: (k9_relat_1(k1_xboole_0, B_260)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1358, c_1640])).
% 4.16/1.71  tff(c_1615, plain, (![A_256, B_257]: (k9_relat_1(k6_relat_1(A_256), B_257)=B_257 | ~m1_subset_1(B_257, k1_zfmisc_1(A_256)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.16/1.71  tff(c_1618, plain, (k9_relat_1(k6_relat_1(k1_xboole_0), '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_1440, c_1615])).
% 4.16/1.71  tff(c_1620, plain, (k9_relat_1(k1_xboole_0, '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1618])).
% 4.16/1.71  tff(c_1649, plain, (k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1645, c_1620])).
% 4.16/1.71  tff(c_1393, plain, (![A_209]: (k1_relat_1(k6_relat_1(A_209))=A_209)), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.16/1.71  tff(c_1402, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_40, c_1393])).
% 4.16/1.71  tff(c_1673, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1649, c_1649, c_1402])).
% 4.16/1.71  tff(c_10, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.16/1.71  tff(c_1431, plain, (![A_213, B_214]: (r1_tarski(k2_relat_1(k2_zfmisc_1(A_213, B_214)), B_214))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.16/1.71  tff(c_1434, plain, (![B_4]: (r1_tarski(k2_relat_1(k1_xboole_0), B_4))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1431])).
% 4.16/1.71  tff(c_1438, plain, (![B_4]: (r1_tarski(k1_xboole_0, B_4))), inference(demodulation, [status(thm), theory('equality')], [c_1358, c_1434])).
% 4.16/1.71  tff(c_1668, plain, (![B_4]: (r1_tarski('#skF_4', B_4))), inference(demodulation, [status(thm), theory('equality')], [c_1649, c_1438])).
% 4.16/1.71  tff(c_1676, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1649, c_1649, c_1358])).
% 4.16/1.71  tff(c_1750, plain, (![B_263, A_264]: (k5_relat_1(B_263, k6_relat_1(A_264))=B_263 | ~r1_tarski(k2_relat_1(B_263), A_264) | ~v1_relat_1(B_263))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.16/1.71  tff(c_1753, plain, (![A_264]: (k5_relat_1('#skF_4', k6_relat_1(A_264))='#skF_4' | ~r1_tarski('#skF_4', A_264) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1676, c_1750])).
% 4.16/1.71  tff(c_1767, plain, (![A_264]: (k5_relat_1('#skF_4', k6_relat_1(A_264))='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1483, c_1668, c_1753])).
% 4.16/1.71  tff(c_1939, plain, (![A_275, B_276]: (k10_relat_1(A_275, k1_relat_1(B_276))=k1_relat_1(k5_relat_1(A_275, B_276)) | ~v1_relat_1(B_276) | ~v1_relat_1(A_275))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.16/1.71  tff(c_1951, plain, (![A_275, A_23]: (k1_relat_1(k5_relat_1(A_275, k6_relat_1(A_23)))=k10_relat_1(A_275, A_23) | ~v1_relat_1(k6_relat_1(A_23)) | ~v1_relat_1(A_275))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1939])).
% 4.16/1.71  tff(c_2072, plain, (![A_299, A_300]: (k1_relat_1(k5_relat_1(A_299, k6_relat_1(A_300)))=k10_relat_1(A_299, A_300) | ~v1_relat_1(A_299))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1951])).
% 4.16/1.71  tff(c_2090, plain, (![A_264]: (k10_relat_1('#skF_4', A_264)=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1767, c_2072])).
% 4.16/1.71  tff(c_2099, plain, (![A_264]: (k10_relat_1('#skF_4', A_264)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1483, c_1673, c_2090])).
% 4.16/1.71  tff(c_1669, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1649, c_1440])).
% 4.16/1.71  tff(c_1674, plain, (![B_4]: (k2_zfmisc_1('#skF_4', B_4)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1649, c_1649, c_10])).
% 4.16/1.71  tff(c_1975, plain, (![A_280, B_281, C_282, D_283]: (k8_relset_1(A_280, B_281, C_282, D_283)=k10_relat_1(C_282, D_283) | ~m1_subset_1(C_282, k1_zfmisc_1(k2_zfmisc_1(A_280, B_281))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.16/1.71  tff(c_2494, plain, (![B_329, C_330, D_331]: (k8_relset_1('#skF_4', B_329, C_330, D_331)=k10_relat_1(C_330, D_331) | ~m1_subset_1(C_330, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_1674, c_1975])).
% 4.16/1.71  tff(c_2496, plain, (![B_329, D_331]: (k8_relset_1('#skF_4', B_329, '#skF_4', D_331)=k10_relat_1('#skF_4', D_331))), inference(resolution, [status(thm)], [c_1669, c_2494])).
% 4.16/1.71  tff(c_2498, plain, (![B_329, D_331]: (k8_relset_1('#skF_4', B_329, '#skF_4', D_331)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2099, c_2496])).
% 4.16/1.71  tff(c_1339, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_68])).
% 4.16/1.71  tff(c_1415, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_78, c_1409])).
% 4.16/1.71  tff(c_1419, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1339, c_1415])).
% 4.16/1.71  tff(c_1484, plain, (k8_relset_1(k1_xboole_0, k1_xboole_0, '#skF_4', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1419, c_1417, c_1340, c_1339, c_66])).
% 4.16/1.71  tff(c_1664, plain, (k8_relset_1('#skF_4', '#skF_4', '#skF_4', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1649, c_1649, c_1649, c_1649, c_1484])).
% 4.16/1.71  tff(c_2501, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2498, c_1664])).
% 4.16/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.16/1.71  
% 4.16/1.71  Inference rules
% 4.16/1.71  ----------------------
% 4.16/1.71  #Ref     : 0
% 4.16/1.71  #Sup     : 537
% 4.16/1.71  #Fact    : 0
% 4.16/1.71  #Define  : 0
% 4.16/1.71  #Split   : 3
% 4.16/1.71  #Chain   : 0
% 4.16/1.71  #Close   : 0
% 4.16/1.71  
% 4.16/1.71  Ordering : KBO
% 4.16/1.71  
% 4.16/1.71  Simplification rules
% 4.16/1.71  ----------------------
% 4.16/1.71  #Subsume      : 42
% 4.16/1.71  #Demod        : 503
% 4.16/1.71  #Tautology    : 341
% 4.16/1.71  #SimpNegUnit  : 2
% 4.16/1.71  #BackRed      : 36
% 4.16/1.71  
% 4.16/1.71  #Partial instantiations: 0
% 4.16/1.71  #Strategies tried      : 1
% 4.16/1.71  
% 4.16/1.71  Timing (in seconds)
% 4.16/1.71  ----------------------
% 4.16/1.71  Preprocessing        : 0.35
% 4.16/1.71  Parsing              : 0.18
% 4.16/1.71  CNF conversion       : 0.02
% 4.16/1.71  Main loop            : 0.59
% 4.16/1.71  Inferencing          : 0.21
% 4.16/1.71  Reduction            : 0.20
% 4.16/1.71  Demodulation         : 0.14
% 4.16/1.71  BG Simplification    : 0.03
% 4.16/1.71  Subsumption          : 0.09
% 4.16/1.71  Abstraction          : 0.03
% 4.16/1.71  MUC search           : 0.00
% 4.16/1.71  Cooper               : 0.00
% 4.16/1.71  Total                : 0.99
% 4.16/1.71  Index Insertion      : 0.00
% 4.16/1.71  Index Deletion       : 0.00
% 4.16/1.71  Index Matching       : 0.00
% 4.16/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
