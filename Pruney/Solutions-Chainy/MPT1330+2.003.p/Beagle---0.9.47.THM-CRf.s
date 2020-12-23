%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:09 EST 2020

% Result     : Theorem 4.09s
% Output     : CNFRefutation 4.48s
% Verified   : 
% Statistics : Number of formulae       :  155 (1022 expanded)
%              Number of leaves         :   53 ( 368 expanded)
%              Depth                    :   15
%              Number of atoms          :  223 (2165 expanded)
%              Number of equality atoms :   90 ( 941 expanded)
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

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_179,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_tops_2)).

tff(f_160,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_139,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_156,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | v1_partfun1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).

tff(f_110,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_52,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_87,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_76,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( v1_xboole_0(A)
        & v1_relat_1(A) )
     => ( v1_xboole_0(k7_relat_1(A,B))
        & v1_relat_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc17_relat_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_73,axiom,(
    ! [A,B] : r1_tarski(k2_relat_1(k2_zfmisc_1(A,B)),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t194_relat_1)).

tff(c_8,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_80,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_173,plain,(
    ! [A_79] :
      ( u1_struct_0(A_79) = k2_struct_0(A_79)
      | ~ l1_struct_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_181,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_173])).

tff(c_78,plain,(
    l1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_180,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_173])).

tff(c_72,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_205,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_180,c_72])).

tff(c_219,plain,(
    ! [C_88,A_89,B_90] :
      ( v1_relat_1(C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_227,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_205,c_219])).

tff(c_267,plain,(
    ! [C_97,A_98,B_99] :
      ( v4_relat_1(C_97,A_98)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_277,plain,(
    v4_relat_1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_205,c_267])).

tff(c_514,plain,(
    ! [B_136,A_137] :
      ( k1_relat_1(B_136) = A_137
      | ~ v1_partfun1(B_136,A_137)
      | ~ v4_relat_1(B_136,A_137)
      | ~ v1_relat_1(B_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_517,plain,
    ( k2_struct_0('#skF_2') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',k2_struct_0('#skF_2'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_277,c_514])).

tff(c_520,plain,
    ( k2_struct_0('#skF_2') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_517])).

tff(c_521,plain,(
    ~ v1_partfun1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_520])).

tff(c_70,plain,
    ( k2_struct_0('#skF_2') = k1_xboole_0
    | k2_struct_0('#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_97,plain,(
    k2_struct_0('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_76,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_74,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_182,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_74])).

tff(c_197,plain,(
    v1_funct_2('#skF_4',k2_struct_0('#skF_2'),k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_182])).

tff(c_802,plain,(
    ! [B_162,C_163,A_164] :
      ( k1_xboole_0 = B_162
      | v1_partfun1(C_163,A_164)
      | ~ v1_funct_2(C_163,A_164,B_162)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(A_164,B_162)))
      | ~ v1_funct_1(C_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_805,plain,
    ( k2_struct_0('#skF_3') = k1_xboole_0
    | v1_partfun1('#skF_4',k2_struct_0('#skF_2'))
    | ~ v1_funct_2('#skF_4',k2_struct_0('#skF_2'),k2_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_205,c_802])).

tff(c_814,plain,
    ( k2_struct_0('#skF_3') = k1_xboole_0
    | v1_partfun1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_197,c_805])).

tff(c_816,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_521,c_97,c_814])).

tff(c_817,plain,(
    k2_struct_0('#skF_2') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_520])).

tff(c_822,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k2_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_817,c_205])).

tff(c_1071,plain,(
    ! [A_177,B_178,C_179,D_180] :
      ( k8_relset_1(A_177,B_178,C_179,D_180) = k10_relat_1(C_179,D_180)
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1(A_177,B_178))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1078,plain,(
    ! [D_180] : k8_relset_1(k1_relat_1('#skF_4'),k2_struct_0('#skF_3'),'#skF_4',D_180) = k10_relat_1('#skF_4',D_180) ),
    inference(resolution,[status(thm)],[c_822,c_1071])).

tff(c_68,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k2_struct_0('#skF_3')) != k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_266,plain,(
    k8_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'),'#skF_4',k2_struct_0('#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_180,c_68])).

tff(c_821,plain,(
    k8_relset_1(k1_relat_1('#skF_4'),k2_struct_0('#skF_3'),'#skF_4',k2_struct_0('#skF_3')) != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_817,c_817,c_266])).

tff(c_1140,plain,(
    k10_relat_1('#skF_4',k2_struct_0('#skF_3')) != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1078,c_821])).

tff(c_362,plain,(
    ! [C_116,B_117,A_118] :
      ( v5_relat_1(C_116,B_117)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_118,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_372,plain,(
    v5_relat_1('#skF_4',k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_205,c_362])).

tff(c_16,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_454,plain,(
    ! [B_131,A_132] :
      ( k5_relat_1(B_131,k6_relat_1(A_132)) = B_131
      | ~ r1_tarski(k2_relat_1(B_131),A_132)
      | ~ v1_relat_1(B_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_470,plain,(
    ! [B_7,A_6] :
      ( k5_relat_1(B_7,k6_relat_1(A_6)) = B_7
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(resolution,[status(thm)],[c_16,c_454])).

tff(c_18,plain,(
    ! [A_8] : v1_relat_1(k6_relat_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_34,plain,(
    ! [A_18] : k1_relat_1(k6_relat_1(A_18)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_847,plain,(
    ! [A_165,B_166] :
      ( k10_relat_1(A_165,k1_relat_1(B_166)) = k1_relat_1(k5_relat_1(A_165,B_166))
      | ~ v1_relat_1(B_166)
      | ~ v1_relat_1(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_856,plain,(
    ! [A_165,A_18] :
      ( k1_relat_1(k5_relat_1(A_165,k6_relat_1(A_18))) = k10_relat_1(A_165,A_18)
      | ~ v1_relat_1(k6_relat_1(A_18))
      | ~ v1_relat_1(A_165) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_847])).

tff(c_970,plain,(
    ! [A_173,A_174] :
      ( k1_relat_1(k5_relat_1(A_173,k6_relat_1(A_174))) = k10_relat_1(A_173,A_174)
      | ~ v1_relat_1(A_173) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_856])).

tff(c_1167,plain,(
    ! [B_195,A_196] :
      ( k10_relat_1(B_195,A_196) = k1_relat_1(B_195)
      | ~ v1_relat_1(B_195)
      | ~ v5_relat_1(B_195,A_196)
      | ~ v1_relat_1(B_195) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_470,c_970])).

tff(c_1173,plain,
    ( k10_relat_1('#skF_4',k2_struct_0('#skF_3')) = k1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_372,c_1167])).

tff(c_1183,plain,(
    k10_relat_1('#skF_4',k2_struct_0('#skF_3')) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_1173])).

tff(c_1185,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1140,c_1183])).

tff(c_1187,plain,(
    k2_struct_0('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_1261,plain,(
    ! [A_205] :
      ( u1_struct_0(A_205) = k2_struct_0(A_205)
      | ~ l1_struct_0(A_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_1264,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_1261])).

tff(c_1269,plain,(
    u1_struct_0('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1187,c_1264])).

tff(c_1272,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1269,c_72])).

tff(c_1274,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1272])).

tff(c_10,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1319,plain,(
    ! [C_215,A_216,B_217] :
      ( v1_relat_1(C_215)
      | ~ m1_subset_1(C_215,k1_zfmisc_1(k2_zfmisc_1(A_216,B_217))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1324,plain,(
    ! [C_218] :
      ( v1_relat_1(C_218)
      | ~ m1_subset_1(C_218,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1319])).

tff(c_1328,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1274,c_1324])).

tff(c_40,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_85,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_18])).

tff(c_30,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1329,plain,(
    ! [A_219,B_220] :
      ( v1_xboole_0(k7_relat_1(A_219,B_220))
      | ~ v1_relat_1(A_219)
      | ~ v1_xboole_0(A_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1290,plain,(
    ! [B_209,A_210] :
      ( ~ v1_xboole_0(B_209)
      | B_209 = A_210
      | ~ v1_xboole_0(A_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1293,plain,(
    ! [A_210] :
      ( k1_xboole_0 = A_210
      | ~ v1_xboole_0(A_210) ) ),
    inference(resolution,[status(thm)],[c_2,c_1290])).

tff(c_1352,plain,(
    ! [A_225,B_226] :
      ( k7_relat_1(A_225,B_226) = k1_xboole_0
      | ~ v1_relat_1(A_225)
      | ~ v1_xboole_0(A_225) ) ),
    inference(resolution,[status(thm)],[c_1329,c_1293])).

tff(c_1356,plain,(
    ! [B_226] :
      ( k7_relat_1(k1_xboole_0,B_226) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2,c_1352])).

tff(c_1360,plain,(
    ! [B_226] : k7_relat_1(k1_xboole_0,B_226) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_1356])).

tff(c_1385,plain,(
    ! [B_231,A_232] :
      ( k2_relat_1(k7_relat_1(B_231,A_232)) = k9_relat_1(B_231,A_232)
      | ~ v1_relat_1(B_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1394,plain,(
    ! [B_226] :
      ( k9_relat_1(k1_xboole_0,B_226) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1360,c_1385])).

tff(c_1399,plain,(
    ! [B_233] : k9_relat_1(k1_xboole_0,B_233) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_30,c_1394])).

tff(c_1342,plain,(
    ! [A_223,B_224] :
      ( k9_relat_1(k6_relat_1(A_223),B_224) = B_224
      | ~ m1_subset_1(B_224,k1_zfmisc_1(A_223)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1345,plain,(
    k9_relat_1(k6_relat_1(k1_xboole_0),'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1274,c_1342])).

tff(c_1347,plain,(
    k9_relat_1(k1_xboole_0,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1345])).

tff(c_1403,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1399,c_1347])).

tff(c_32,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1429,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1403,c_1403,c_32])).

tff(c_1250,plain,(
    ! [A_202,B_203] : r1_tarski(k2_relat_1(k2_zfmisc_1(A_202,B_203)),B_203) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1253,plain,(
    ! [B_4] : r1_tarski(k2_relat_1(k1_xboole_0),B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1250])).

tff(c_1257,plain,(
    ! [B_4] : r1_tarski(k1_xboole_0,B_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1253])).

tff(c_1424,plain,(
    ! [B_4] : r1_tarski('#skF_4',B_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1403,c_1257])).

tff(c_1430,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1403,c_1403,c_30])).

tff(c_1763,plain,(
    ! [B_269,A_270] :
      ( k5_relat_1(B_269,k6_relat_1(A_270)) = B_269
      | ~ r1_tarski(k2_relat_1(B_269),A_270)
      | ~ v1_relat_1(B_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1769,plain,(
    ! [A_270] :
      ( k5_relat_1('#skF_4',k6_relat_1(A_270)) = '#skF_4'
      | ~ r1_tarski('#skF_4',A_270)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1430,c_1763])).

tff(c_1781,plain,(
    ! [A_270] : k5_relat_1('#skF_4',k6_relat_1(A_270)) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1328,c_1424,c_1769])).

tff(c_1805,plain,(
    ! [A_273,B_274] :
      ( k10_relat_1(A_273,k1_relat_1(B_274)) = k1_relat_1(k5_relat_1(A_273,B_274))
      | ~ v1_relat_1(B_274)
      | ~ v1_relat_1(A_273) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1817,plain,(
    ! [A_273,A_18] :
      ( k1_relat_1(k5_relat_1(A_273,k6_relat_1(A_18))) = k10_relat_1(A_273,A_18)
      | ~ v1_relat_1(k6_relat_1(A_18))
      | ~ v1_relat_1(A_273) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1805])).

tff(c_2076,plain,(
    ! [A_317,A_318] :
      ( k1_relat_1(k5_relat_1(A_317,k6_relat_1(A_318))) = k10_relat_1(A_317,A_318)
      | ~ v1_relat_1(A_317) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1817])).

tff(c_2097,plain,(
    ! [A_270] :
      ( k10_relat_1('#skF_4',A_270) = k1_relat_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1781,c_2076])).

tff(c_2106,plain,(
    ! [A_270] : k10_relat_1('#skF_4',A_270) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1328,c_1429,c_2097])).

tff(c_1421,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1403,c_1274])).

tff(c_1426,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1403,c_1403,c_8])).

tff(c_1878,plain,(
    ! [A_286,B_287,C_288,D_289] :
      ( k8_relset_1(A_286,B_287,C_288,D_289) = k10_relat_1(C_288,D_289)
      | ~ m1_subset_1(C_288,k1_zfmisc_1(k2_zfmisc_1(A_286,B_287))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2361,plain,(
    ! [A_331,C_332,D_333] :
      ( k8_relset_1(A_331,'#skF_4',C_332,D_333) = k10_relat_1(C_332,D_333)
      | ~ m1_subset_1(C_332,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1426,c_1878])).

tff(c_2363,plain,(
    ! [A_331,D_333] : k8_relset_1(A_331,'#skF_4','#skF_4',D_333) = k10_relat_1('#skF_4',D_333) ),
    inference(resolution,[status(thm)],[c_1421,c_2361])).

tff(c_2365,plain,(
    ! [A_331,D_333] : k8_relset_1(A_331,'#skF_4','#skF_4',D_333) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2106,c_2363])).

tff(c_1186,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_1267,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_1261])).

tff(c_1271,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1186,c_1267])).

tff(c_1294,plain,(
    k8_relset_1(k1_xboole_0,k1_xboole_0,'#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1271,c_1269,c_1187,c_1186,c_68])).

tff(c_1418,plain,(
    k8_relset_1('#skF_4','#skF_4','#skF_4','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1403,c_1403,c_1403,c_1403,c_1294])).

tff(c_2368,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2365,c_1418])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.36  % Computer   : n023.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 13:21:21 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.09/1.73  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.09/1.75  
% 4.09/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.09/1.75  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k6_relat_1 > k2_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 4.09/1.75  
% 4.09/1.75  %Foreground sorts:
% 4.09/1.75  
% 4.09/1.75  
% 4.09/1.75  %Background operators:
% 4.09/1.75  
% 4.09/1.75  
% 4.09/1.75  %Foreground operators:
% 4.09/1.75  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.09/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.09/1.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.09/1.75  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.09/1.75  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 4.09/1.75  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.09/1.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.09/1.75  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.09/1.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.09/1.75  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.09/1.75  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.09/1.75  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.09/1.75  tff('#skF_2', type, '#skF_2': $i).
% 4.09/1.75  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.09/1.75  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.09/1.75  tff('#skF_3', type, '#skF_3': $i).
% 4.09/1.75  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.09/1.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.09/1.75  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.09/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.09/1.75  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.09/1.75  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.09/1.75  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.09/1.75  tff('#skF_4', type, '#skF_4': $i).
% 4.09/1.75  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.09/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.09/1.75  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.09/1.75  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.09/1.75  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.09/1.75  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.09/1.75  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.09/1.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.09/1.75  
% 4.48/1.77  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.48/1.77  tff(f_179, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_struct_0(B) = k1_xboole_0) => (k2_struct_0(A) = k1_xboole_0)) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k2_struct_0(B)) = k2_struct_0(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_tops_2)).
% 4.48/1.77  tff(f_160, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 4.48/1.77  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.48/1.77  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.48/1.77  tff(f_139, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 4.48/1.77  tff(f_156, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_funct_2)).
% 4.48/1.77  tff(f_110, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 4.48/1.77  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 4.48/1.77  tff(f_86, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 4.48/1.77  tff(f_52, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 4.48/1.77  tff(f_80, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 4.48/1.77  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 4.48/1.77  tff(f_87, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 4.48/1.77  tff(f_76, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 4.48/1.77  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.48/1.77  tff(f_60, axiom, (![A, B]: ((v1_xboole_0(A) & v1_relat_1(A)) => (v1_xboole_0(k7_relat_1(A, B)) & v1_relat_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc17_relat_1)).
% 4.48/1.77  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 4.48/1.77  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 4.48/1.77  tff(f_91, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_funct_1)).
% 4.48/1.77  tff(f_73, axiom, (![A, B]: r1_tarski(k2_relat_1(k2_zfmisc_1(A, B)), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t194_relat_1)).
% 4.48/1.77  tff(c_8, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.48/1.77  tff(c_80, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_179])).
% 4.48/1.77  tff(c_173, plain, (![A_79]: (u1_struct_0(A_79)=k2_struct_0(A_79) | ~l1_struct_0(A_79))), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.48/1.77  tff(c_181, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_80, c_173])).
% 4.48/1.77  tff(c_78, plain, (l1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_179])).
% 4.48/1.77  tff(c_180, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_78, c_173])).
% 4.48/1.77  tff(c_72, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_179])).
% 4.48/1.77  tff(c_205, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_181, c_180, c_72])).
% 4.48/1.77  tff(c_219, plain, (![C_88, A_89, B_90]: (v1_relat_1(C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.48/1.77  tff(c_227, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_205, c_219])).
% 4.48/1.77  tff(c_267, plain, (![C_97, A_98, B_99]: (v4_relat_1(C_97, A_98) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.48/1.77  tff(c_277, plain, (v4_relat_1('#skF_4', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_205, c_267])).
% 4.48/1.77  tff(c_514, plain, (![B_136, A_137]: (k1_relat_1(B_136)=A_137 | ~v1_partfun1(B_136, A_137) | ~v4_relat_1(B_136, A_137) | ~v1_relat_1(B_136))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.48/1.77  tff(c_517, plain, (k2_struct_0('#skF_2')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', k2_struct_0('#skF_2')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_277, c_514])).
% 4.48/1.77  tff(c_520, plain, (k2_struct_0('#skF_2')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_227, c_517])).
% 4.48/1.77  tff(c_521, plain, (~v1_partfun1('#skF_4', k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_520])).
% 4.48/1.77  tff(c_70, plain, (k2_struct_0('#skF_2')=k1_xboole_0 | k2_struct_0('#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_179])).
% 4.48/1.77  tff(c_97, plain, (k2_struct_0('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_70])).
% 4.48/1.77  tff(c_76, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_179])).
% 4.48/1.77  tff(c_74, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_179])).
% 4.48/1.77  tff(c_182, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_180, c_74])).
% 4.48/1.77  tff(c_197, plain, (v1_funct_2('#skF_4', k2_struct_0('#skF_2'), k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_181, c_182])).
% 4.48/1.77  tff(c_802, plain, (![B_162, C_163, A_164]: (k1_xboole_0=B_162 | v1_partfun1(C_163, A_164) | ~v1_funct_2(C_163, A_164, B_162) | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(A_164, B_162))) | ~v1_funct_1(C_163))), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.48/1.77  tff(c_805, plain, (k2_struct_0('#skF_3')=k1_xboole_0 | v1_partfun1('#skF_4', k2_struct_0('#skF_2')) | ~v1_funct_2('#skF_4', k2_struct_0('#skF_2'), k2_struct_0('#skF_3')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_205, c_802])).
% 4.48/1.77  tff(c_814, plain, (k2_struct_0('#skF_3')=k1_xboole_0 | v1_partfun1('#skF_4', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_197, c_805])).
% 4.48/1.77  tff(c_816, plain, $false, inference(negUnitSimplification, [status(thm)], [c_521, c_97, c_814])).
% 4.48/1.77  tff(c_817, plain, (k2_struct_0('#skF_2')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_520])).
% 4.48/1.77  tff(c_822, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_817, c_205])).
% 4.48/1.77  tff(c_1071, plain, (![A_177, B_178, C_179, D_180]: (k8_relset_1(A_177, B_178, C_179, D_180)=k10_relat_1(C_179, D_180) | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1(A_177, B_178))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.48/1.77  tff(c_1078, plain, (![D_180]: (k8_relset_1(k1_relat_1('#skF_4'), k2_struct_0('#skF_3'), '#skF_4', D_180)=k10_relat_1('#skF_4', D_180))), inference(resolution, [status(thm)], [c_822, c_1071])).
% 4.48/1.77  tff(c_68, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k2_struct_0('#skF_3'))!=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_179])).
% 4.48/1.77  tff(c_266, plain, (k8_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'), '#skF_4', k2_struct_0('#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_181, c_180, c_68])).
% 4.48/1.77  tff(c_821, plain, (k8_relset_1(k1_relat_1('#skF_4'), k2_struct_0('#skF_3'), '#skF_4', k2_struct_0('#skF_3'))!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_817, c_817, c_266])).
% 4.48/1.77  tff(c_1140, plain, (k10_relat_1('#skF_4', k2_struct_0('#skF_3'))!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1078, c_821])).
% 4.48/1.77  tff(c_362, plain, (![C_116, B_117, A_118]: (v5_relat_1(C_116, B_117) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_118, B_117))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.48/1.77  tff(c_372, plain, (v5_relat_1('#skF_4', k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_205, c_362])).
% 4.48/1.77  tff(c_16, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.48/1.77  tff(c_454, plain, (![B_131, A_132]: (k5_relat_1(B_131, k6_relat_1(A_132))=B_131 | ~r1_tarski(k2_relat_1(B_131), A_132) | ~v1_relat_1(B_131))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.48/1.77  tff(c_470, plain, (![B_7, A_6]: (k5_relat_1(B_7, k6_relat_1(A_6))=B_7 | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(resolution, [status(thm)], [c_16, c_454])).
% 4.48/1.77  tff(c_18, plain, (![A_8]: (v1_relat_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.48/1.77  tff(c_34, plain, (![A_18]: (k1_relat_1(k6_relat_1(A_18))=A_18)), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.48/1.77  tff(c_847, plain, (![A_165, B_166]: (k10_relat_1(A_165, k1_relat_1(B_166))=k1_relat_1(k5_relat_1(A_165, B_166)) | ~v1_relat_1(B_166) | ~v1_relat_1(A_165))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.48/1.77  tff(c_856, plain, (![A_165, A_18]: (k1_relat_1(k5_relat_1(A_165, k6_relat_1(A_18)))=k10_relat_1(A_165, A_18) | ~v1_relat_1(k6_relat_1(A_18)) | ~v1_relat_1(A_165))), inference(superposition, [status(thm), theory('equality')], [c_34, c_847])).
% 4.48/1.77  tff(c_970, plain, (![A_173, A_174]: (k1_relat_1(k5_relat_1(A_173, k6_relat_1(A_174)))=k10_relat_1(A_173, A_174) | ~v1_relat_1(A_173))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_856])).
% 4.48/1.77  tff(c_1167, plain, (![B_195, A_196]: (k10_relat_1(B_195, A_196)=k1_relat_1(B_195) | ~v1_relat_1(B_195) | ~v5_relat_1(B_195, A_196) | ~v1_relat_1(B_195))), inference(superposition, [status(thm), theory('equality')], [c_470, c_970])).
% 4.48/1.77  tff(c_1173, plain, (k10_relat_1('#skF_4', k2_struct_0('#skF_3'))=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_372, c_1167])).
% 4.48/1.77  tff(c_1183, plain, (k10_relat_1('#skF_4', k2_struct_0('#skF_3'))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_227, c_1173])).
% 4.48/1.77  tff(c_1185, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1140, c_1183])).
% 4.48/1.77  tff(c_1187, plain, (k2_struct_0('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_70])).
% 4.48/1.77  tff(c_1261, plain, (![A_205]: (u1_struct_0(A_205)=k2_struct_0(A_205) | ~l1_struct_0(A_205))), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.48/1.77  tff(c_1264, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_78, c_1261])).
% 4.48/1.77  tff(c_1269, plain, (u1_struct_0('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1187, c_1264])).
% 4.48/1.77  tff(c_1272, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_1269, c_72])).
% 4.48/1.77  tff(c_1274, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1272])).
% 4.48/1.77  tff(c_10, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.48/1.77  tff(c_1319, plain, (![C_215, A_216, B_217]: (v1_relat_1(C_215) | ~m1_subset_1(C_215, k1_zfmisc_1(k2_zfmisc_1(A_216, B_217))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.48/1.77  tff(c_1324, plain, (![C_218]: (v1_relat_1(C_218) | ~m1_subset_1(C_218, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1319])).
% 4.48/1.77  tff(c_1328, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1274, c_1324])).
% 4.48/1.77  tff(c_40, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.48/1.77  tff(c_85, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_40, c_18])).
% 4.48/1.77  tff(c_30, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.48/1.77  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.48/1.77  tff(c_1329, plain, (![A_219, B_220]: (v1_xboole_0(k7_relat_1(A_219, B_220)) | ~v1_relat_1(A_219) | ~v1_xboole_0(A_219))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.48/1.77  tff(c_1290, plain, (![B_209, A_210]: (~v1_xboole_0(B_209) | B_209=A_210 | ~v1_xboole_0(A_210))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.48/1.77  tff(c_1293, plain, (![A_210]: (k1_xboole_0=A_210 | ~v1_xboole_0(A_210))), inference(resolution, [status(thm)], [c_2, c_1290])).
% 4.48/1.77  tff(c_1352, plain, (![A_225, B_226]: (k7_relat_1(A_225, B_226)=k1_xboole_0 | ~v1_relat_1(A_225) | ~v1_xboole_0(A_225))), inference(resolution, [status(thm)], [c_1329, c_1293])).
% 4.48/1.77  tff(c_1356, plain, (![B_226]: (k7_relat_1(k1_xboole_0, B_226)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_1352])).
% 4.48/1.77  tff(c_1360, plain, (![B_226]: (k7_relat_1(k1_xboole_0, B_226)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_85, c_1356])).
% 4.48/1.77  tff(c_1385, plain, (![B_231, A_232]: (k2_relat_1(k7_relat_1(B_231, A_232))=k9_relat_1(B_231, A_232) | ~v1_relat_1(B_231))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.48/1.77  tff(c_1394, plain, (![B_226]: (k9_relat_1(k1_xboole_0, B_226)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1360, c_1385])).
% 4.48/1.77  tff(c_1399, plain, (![B_233]: (k9_relat_1(k1_xboole_0, B_233)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_85, c_30, c_1394])).
% 4.48/1.77  tff(c_1342, plain, (![A_223, B_224]: (k9_relat_1(k6_relat_1(A_223), B_224)=B_224 | ~m1_subset_1(B_224, k1_zfmisc_1(A_223)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.48/1.77  tff(c_1345, plain, (k9_relat_1(k6_relat_1(k1_xboole_0), '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_1274, c_1342])).
% 4.48/1.77  tff(c_1347, plain, (k9_relat_1(k1_xboole_0, '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1345])).
% 4.48/1.77  tff(c_1403, plain, (k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1399, c_1347])).
% 4.48/1.77  tff(c_32, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.48/1.77  tff(c_1429, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1403, c_1403, c_32])).
% 4.48/1.77  tff(c_1250, plain, (![A_202, B_203]: (r1_tarski(k2_relat_1(k2_zfmisc_1(A_202, B_203)), B_203))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.48/1.77  tff(c_1253, plain, (![B_4]: (r1_tarski(k2_relat_1(k1_xboole_0), B_4))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1250])).
% 4.48/1.77  tff(c_1257, plain, (![B_4]: (r1_tarski(k1_xboole_0, B_4))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1253])).
% 4.48/1.77  tff(c_1424, plain, (![B_4]: (r1_tarski('#skF_4', B_4))), inference(demodulation, [status(thm), theory('equality')], [c_1403, c_1257])).
% 4.48/1.77  tff(c_1430, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1403, c_1403, c_30])).
% 4.48/1.77  tff(c_1763, plain, (![B_269, A_270]: (k5_relat_1(B_269, k6_relat_1(A_270))=B_269 | ~r1_tarski(k2_relat_1(B_269), A_270) | ~v1_relat_1(B_269))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.48/1.77  tff(c_1769, plain, (![A_270]: (k5_relat_1('#skF_4', k6_relat_1(A_270))='#skF_4' | ~r1_tarski('#skF_4', A_270) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1430, c_1763])).
% 4.48/1.77  tff(c_1781, plain, (![A_270]: (k5_relat_1('#skF_4', k6_relat_1(A_270))='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1328, c_1424, c_1769])).
% 4.48/1.77  tff(c_1805, plain, (![A_273, B_274]: (k10_relat_1(A_273, k1_relat_1(B_274))=k1_relat_1(k5_relat_1(A_273, B_274)) | ~v1_relat_1(B_274) | ~v1_relat_1(A_273))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.48/1.77  tff(c_1817, plain, (![A_273, A_18]: (k1_relat_1(k5_relat_1(A_273, k6_relat_1(A_18)))=k10_relat_1(A_273, A_18) | ~v1_relat_1(k6_relat_1(A_18)) | ~v1_relat_1(A_273))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1805])).
% 4.48/1.77  tff(c_2076, plain, (![A_317, A_318]: (k1_relat_1(k5_relat_1(A_317, k6_relat_1(A_318)))=k10_relat_1(A_317, A_318) | ~v1_relat_1(A_317))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1817])).
% 4.48/1.77  tff(c_2097, plain, (![A_270]: (k10_relat_1('#skF_4', A_270)=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1781, c_2076])).
% 4.48/1.77  tff(c_2106, plain, (![A_270]: (k10_relat_1('#skF_4', A_270)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1328, c_1429, c_2097])).
% 4.48/1.77  tff(c_1421, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1403, c_1274])).
% 4.48/1.77  tff(c_1426, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1403, c_1403, c_8])).
% 4.48/1.77  tff(c_1878, plain, (![A_286, B_287, C_288, D_289]: (k8_relset_1(A_286, B_287, C_288, D_289)=k10_relat_1(C_288, D_289) | ~m1_subset_1(C_288, k1_zfmisc_1(k2_zfmisc_1(A_286, B_287))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.48/1.77  tff(c_2361, plain, (![A_331, C_332, D_333]: (k8_relset_1(A_331, '#skF_4', C_332, D_333)=k10_relat_1(C_332, D_333) | ~m1_subset_1(C_332, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_1426, c_1878])).
% 4.48/1.77  tff(c_2363, plain, (![A_331, D_333]: (k8_relset_1(A_331, '#skF_4', '#skF_4', D_333)=k10_relat_1('#skF_4', D_333))), inference(resolution, [status(thm)], [c_1421, c_2361])).
% 4.48/1.77  tff(c_2365, plain, (![A_331, D_333]: (k8_relset_1(A_331, '#skF_4', '#skF_4', D_333)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2106, c_2363])).
% 4.48/1.77  tff(c_1186, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_70])).
% 4.48/1.77  tff(c_1267, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_80, c_1261])).
% 4.48/1.77  tff(c_1271, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1186, c_1267])).
% 4.48/1.77  tff(c_1294, plain, (k8_relset_1(k1_xboole_0, k1_xboole_0, '#skF_4', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1271, c_1269, c_1187, c_1186, c_68])).
% 4.48/1.77  tff(c_1418, plain, (k8_relset_1('#skF_4', '#skF_4', '#skF_4', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1403, c_1403, c_1403, c_1403, c_1294])).
% 4.48/1.77  tff(c_2368, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2365, c_1418])).
% 4.48/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.48/1.77  
% 4.48/1.77  Inference rules
% 4.48/1.77  ----------------------
% 4.48/1.77  #Ref     : 0
% 4.48/1.77  #Sup     : 507
% 4.48/1.77  #Fact    : 0
% 4.48/1.77  #Define  : 0
% 4.48/1.77  #Split   : 4
% 4.48/1.77  #Chain   : 0
% 4.48/1.77  #Close   : 0
% 4.48/1.77  
% 4.48/1.77  Ordering : KBO
% 4.48/1.77  
% 4.48/1.77  Simplification rules
% 4.48/1.77  ----------------------
% 4.48/1.77  #Subsume      : 44
% 4.48/1.77  #Demod        : 460
% 4.48/1.77  #Tautology    : 317
% 4.48/1.77  #SimpNegUnit  : 4
% 4.48/1.77  #BackRed      : 36
% 4.48/1.77  
% 4.48/1.77  #Partial instantiations: 0
% 4.48/1.77  #Strategies tried      : 1
% 4.48/1.77  
% 4.48/1.77  Timing (in seconds)
% 4.48/1.77  ----------------------
% 4.48/1.77  Preprocessing        : 0.37
% 4.48/1.77  Parsing              : 0.19
% 4.48/1.77  CNF conversion       : 0.03
% 4.48/1.77  Main loop            : 0.61
% 4.48/1.77  Inferencing          : 0.24
% 4.48/1.77  Reduction            : 0.20
% 4.48/1.77  Demodulation         : 0.14
% 4.48/1.77  BG Simplification    : 0.03
% 4.48/1.77  Subsumption          : 0.09
% 4.48/1.77  Abstraction          : 0.04
% 4.48/1.77  MUC search           : 0.00
% 4.48/1.77  Cooper               : 0.00
% 4.48/1.77  Total                : 1.02
% 4.48/1.77  Index Insertion      : 0.00
% 4.48/1.77  Index Deletion       : 0.00
% 4.48/1.77  Index Matching       : 0.00
% 4.48/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
