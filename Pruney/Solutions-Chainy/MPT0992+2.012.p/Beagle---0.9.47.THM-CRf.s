%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:32 EST 2020

% Result     : Theorem 25.82s
% Output     : CNFRefutation 25.82s
% Verified   : 
% Statistics : Number of formulae       :  196 (2712 expanded)
%              Number of leaves         :   41 ( 834 expanded)
%              Depth                    :   15
%              Number of atoms          :  332 (8189 expanded)
%              Number of equality atoms :   77 (3058 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_161,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(C,A)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(k2_partfun1(A,B,D,C))
              & v1_funct_2(k2_partfun1(A,B,D,C),C,B)
              & m1_subset_1(k2_partfun1(A,B,D,C),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_115,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_129,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_123,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_141,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_93,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_46,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_38,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_74,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_76,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_128,plain,(
    ! [C_51,A_52,B_53] :
      ( v1_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_140,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_128])).

tff(c_72,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_104,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_78,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_81445,plain,(
    ! [A_2044,B_2045,C_2046] :
      ( k1_relset_1(A_2044,B_2045,C_2046) = k1_relat_1(C_2046)
      | ~ m1_subset_1(C_2046,k1_zfmisc_1(k2_zfmisc_1(A_2044,B_2045))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_81463,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_81445])).

tff(c_81773,plain,(
    ! [B_2090,A_2091,C_2092] :
      ( k1_xboole_0 = B_2090
      | k1_relset_1(A_2091,B_2090,C_2092) = A_2091
      | ~ v1_funct_2(C_2092,A_2091,B_2090)
      | ~ m1_subset_1(C_2092,k1_zfmisc_1(k2_zfmisc_1(A_2091,B_2090))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_81779,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_81773])).

tff(c_81793,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_81463,c_81779])).

tff(c_81794,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_81793])).

tff(c_32,plain,(
    ! [B_14,A_13] :
      ( k1_relat_1(k7_relat_1(B_14,A_13)) = A_13
      | ~ r1_tarski(A_13,k1_relat_1(B_14))
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_81814,plain,(
    ! [A_13] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_13)) = A_13
      | ~ r1_tarski(A_13,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81794,c_32])).

tff(c_81826,plain,(
    ! [A_13] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_13)) = A_13
      | ~ r1_tarski(A_13,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_81814])).

tff(c_80,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_81730,plain,(
    ! [A_2084,B_2085,C_2086,D_2087] :
      ( k2_partfun1(A_2084,B_2085,C_2086,D_2087) = k7_relat_1(C_2086,D_2087)
      | ~ m1_subset_1(C_2086,k1_zfmisc_1(k2_zfmisc_1(A_2084,B_2085)))
      | ~ v1_funct_1(C_2086) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_81736,plain,(
    ! [D_2087] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_2087) = k7_relat_1('#skF_4',D_2087)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_76,c_81730])).

tff(c_81750,plain,(
    ! [D_2087] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_2087) = k7_relat_1('#skF_4',D_2087) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_81736])).

tff(c_1160,plain,(
    ! [A_196,B_197,C_198,D_199] :
      ( k2_partfun1(A_196,B_197,C_198,D_199) = k7_relat_1(C_198,D_199)
      | ~ m1_subset_1(C_198,k1_zfmisc_1(k2_zfmisc_1(A_196,B_197)))
      | ~ v1_funct_1(C_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1164,plain,(
    ! [D_199] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_199) = k7_relat_1('#skF_4',D_199)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_76,c_1160])).

tff(c_1175,plain,(
    ! [D_199] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_199) = k7_relat_1('#skF_4',D_199) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1164])).

tff(c_1529,plain,(
    ! [A_223,B_224,C_225,D_226] :
      ( m1_subset_1(k2_partfun1(A_223,B_224,C_225,D_226),k1_zfmisc_1(k2_zfmisc_1(A_223,B_224)))
      | ~ m1_subset_1(C_225,k1_zfmisc_1(k2_zfmisc_1(A_223,B_224)))
      | ~ v1_funct_1(C_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1565,plain,(
    ! [D_199] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_199),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1175,c_1529])).

tff(c_1642,plain,(
    ! [D_233] : m1_subset_1(k7_relat_1('#skF_4',D_233),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_1565])).

tff(c_36,plain,(
    ! [C_20,A_18,B_19] :
      ( v1_relat_1(C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1692,plain,(
    ! [D_233] : v1_relat_1(k7_relat_1('#skF_4',D_233)) ),
    inference(resolution,[status(thm)],[c_1642,c_36])).

tff(c_38,plain,(
    ! [C_23,B_22,A_21] :
      ( v5_relat_1(C_23,B_22)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1691,plain,(
    ! [D_233] : v5_relat_1(k7_relat_1('#skF_4',D_233),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1642,c_38])).

tff(c_26,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k2_relat_1(B_12),A_11)
      | ~ v5_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1069,plain,(
    ! [A_182,B_183,C_184,D_185] :
      ( v1_funct_1(k2_partfun1(A_182,B_183,C_184,D_185))
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(A_182,B_183)))
      | ~ v1_funct_1(C_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1071,plain,(
    ! [D_185] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_185))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_76,c_1069])).

tff(c_1081,plain,(
    ! [D_185] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_185)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1071])).

tff(c_1179,plain,(
    ! [D_185] : v1_funct_1(k7_relat_1('#skF_4',D_185)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1175,c_1081])).

tff(c_874,plain,(
    ! [A_161,B_162,C_163] :
      ( k1_relset_1(A_161,B_162,C_163) = k1_relat_1(C_163)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(A_161,B_162))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_888,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_874])).

tff(c_1202,plain,(
    ! [B_206,A_207,C_208] :
      ( k1_xboole_0 = B_206
      | k1_relset_1(A_207,B_206,C_208) = A_207
      | ~ v1_funct_2(C_208,A_207,B_206)
      | ~ m1_subset_1(C_208,k1_zfmisc_1(k2_zfmisc_1(A_207,B_206))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1208,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_1202])).

tff(c_1222,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_888,c_1208])).

tff(c_1223,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_1222])).

tff(c_1240,plain,(
    ! [A_13] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_13)) = A_13
      | ~ r1_tarski(A_13,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1223,c_32])).

tff(c_1313,plain,(
    ! [A_213] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_213)) = A_213
      | ~ r1_tarski(A_213,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_1240])).

tff(c_64,plain,(
    ! [B_43,A_42] :
      ( m1_subset_1(B_43,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_43),A_42)))
      | ~ r1_tarski(k2_relat_1(B_43),A_42)
      | ~ v1_funct_1(B_43)
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_1322,plain,(
    ! [A_213,A_42] :
      ( m1_subset_1(k7_relat_1('#skF_4',A_213),k1_zfmisc_1(k2_zfmisc_1(A_213,A_42)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_213)),A_42)
      | ~ v1_funct_1(k7_relat_1('#skF_4',A_213))
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_213))
      | ~ r1_tarski(A_213,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1313,c_64])).

tff(c_1359,plain,(
    ! [A_213,A_42] :
      ( m1_subset_1(k7_relat_1('#skF_4',A_213),k1_zfmisc_1(k2_zfmisc_1(A_213,A_42)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_213)),A_42)
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_213))
      | ~ r1_tarski(A_213,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1179,c_1322])).

tff(c_80998,plain,(
    ! [A_2004,A_2005] :
      ( m1_subset_1(k7_relat_1('#skF_4',A_2004),k1_zfmisc_1(k2_zfmisc_1(A_2004,A_2005)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_2004)),A_2005)
      | ~ r1_tarski(A_2004,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1692,c_1359])).

tff(c_591,plain,(
    ! [A_115,B_116,C_117,D_118] :
      ( v1_funct_1(k2_partfun1(A_115,B_116,C_117,D_118))
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116)))
      | ~ v1_funct_1(C_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_593,plain,(
    ! [D_118] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_118))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_76,c_591])).

tff(c_603,plain,(
    ! [D_118] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_118)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_593])).

tff(c_70,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_142,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_609,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_603,c_142])).

tff(c_610,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_657,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_610])).

tff(c_1180,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1175,c_657])).

tff(c_81036,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2')
    | ~ r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_80998,c_1180])).

tff(c_81110,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_81036])).

tff(c_81145,plain,
    ( ~ v5_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_26,c_81110])).

tff(c_81157,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1692,c_1691,c_81145])).

tff(c_81159,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_610])).

tff(c_81462,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) = k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_81159,c_81445])).

tff(c_81756,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81750,c_81750,c_81462])).

tff(c_81158,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_610])).

tff(c_81762,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81750,c_81158])).

tff(c_81761,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81750,c_81159])).

tff(c_81934,plain,(
    ! [B_2100,C_2101,A_2102] :
      ( k1_xboole_0 = B_2100
      | v1_funct_2(C_2101,A_2102,B_2100)
      | k1_relset_1(A_2102,B_2100,C_2101) != A_2102
      | ~ m1_subset_1(C_2101,k1_zfmisc_1(k2_zfmisc_1(A_2102,B_2100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_81937,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_81761,c_81934])).

tff(c_81956,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_81762,c_104,c_81937])).

tff(c_82190,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_81756,c_81956])).

tff(c_82197,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_81826,c_82190])).

tff(c_82201,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_82197])).

tff(c_82202,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_18,plain,(
    ! [B_6] : k2_zfmisc_1(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_82236,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_1',B_6) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82202,c_82202,c_18])).

tff(c_82203,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_82213,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82202,c_82203])).

tff(c_82228,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82213,c_76])).

tff(c_82237,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82236,c_82228])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_82208,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82202,c_2])).

tff(c_84301,plain,(
    ! [C_2368,A_2369,B_2370] :
      ( v1_xboole_0(C_2368)
      | ~ m1_subset_1(C_2368,k1_zfmisc_1(k2_zfmisc_1(A_2369,B_2370)))
      | ~ v1_xboole_0(A_2369) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_84311,plain,(
    ! [C_2368] :
      ( v1_xboole_0(C_2368)
      | ~ m1_subset_1(C_2368,k1_zfmisc_1('#skF_1'))
      | ~ v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82236,c_84301])).

tff(c_84316,plain,(
    ! [C_2371] :
      ( v1_xboole_0(C_2371)
      | ~ m1_subset_1(C_2371,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82208,c_84311])).

tff(c_84328,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_82237,c_84316])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_82229,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82202,c_4])).

tff(c_84334,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_84328,c_82229])).

tff(c_82214,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82213,c_78])).

tff(c_84361,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84334,c_84334,c_82214])).

tff(c_83010,plain,(
    ! [C_2224,A_2225,B_2226] :
      ( v1_xboole_0(C_2224)
      | ~ m1_subset_1(C_2224,k1_zfmisc_1(k2_zfmisc_1(A_2225,B_2226)))
      | ~ v1_xboole_0(A_2225) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_83020,plain,(
    ! [C_2224] :
      ( v1_xboole_0(C_2224)
      | ~ m1_subset_1(C_2224,k1_zfmisc_1('#skF_1'))
      | ~ v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82236,c_83010])).

tff(c_83025,plain,(
    ! [C_2227] :
      ( v1_xboole_0(C_2227)
      | ~ m1_subset_1(C_2227,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82208,c_83020])).

tff(c_83033,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_82237,c_83025])).

tff(c_83039,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_83033,c_82229])).

tff(c_20,plain,(
    ! [A_7] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_82245,plain,(
    ! [A_7] : m1_subset_1('#skF_1',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82202,c_20])).

tff(c_83058,plain,(
    ! [A_7] : m1_subset_1('#skF_4',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83039,c_82245])).

tff(c_83656,plain,(
    ! [A_2294,B_2295,C_2296,D_2297] :
      ( k2_partfun1(A_2294,B_2295,C_2296,D_2297) = k7_relat_1(C_2296,D_2297)
      | ~ m1_subset_1(C_2296,k1_zfmisc_1(k2_zfmisc_1(A_2294,B_2295)))
      | ~ v1_funct_1(C_2296) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_83665,plain,(
    ! [A_2294,B_2295,D_2297] :
      ( k2_partfun1(A_2294,B_2295,'#skF_4',D_2297) = k7_relat_1('#skF_4',D_2297)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_83058,c_83656])).

tff(c_83669,plain,(
    ! [A_2294,B_2295,D_2297] : k2_partfun1(A_2294,B_2295,'#skF_4',D_2297) = k7_relat_1('#skF_4',D_2297) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_83665])).

tff(c_84002,plain,(
    ! [A_2336,B_2337,C_2338,D_2339] :
      ( m1_subset_1(k2_partfun1(A_2336,B_2337,C_2338,D_2339),k1_zfmisc_1(k2_zfmisc_1(A_2336,B_2337)))
      | ~ m1_subset_1(C_2338,k1_zfmisc_1(k2_zfmisc_1(A_2336,B_2337)))
      | ~ v1_funct_1(C_2338) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_84035,plain,(
    ! [D_2297,A_2294,B_2295] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_2297),k1_zfmisc_1(k2_zfmisc_1(A_2294,B_2295)))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_2294,B_2295)))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83669,c_84002])).

tff(c_84057,plain,(
    ! [D_2340,A_2341,B_2342] : m1_subset_1(k7_relat_1('#skF_4',D_2340),k1_zfmisc_1(k2_zfmisc_1(A_2341,B_2342))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_83058,c_84035])).

tff(c_84106,plain,(
    ! [D_2340,B_2342] : v5_relat_1(k7_relat_1('#skF_4',D_2340),B_2342) ),
    inference(resolution,[status(thm)],[c_84057,c_38])).

tff(c_83825,plain,(
    ! [A_2318,B_2319,C_2320,D_2321] :
      ( m1_subset_1(k2_partfun1(A_2318,B_2319,C_2320,D_2321),k1_zfmisc_1(k2_zfmisc_1(A_2318,B_2319)))
      | ~ m1_subset_1(C_2320,k1_zfmisc_1(k2_zfmisc_1(A_2318,B_2319)))
      | ~ v1_funct_1(C_2320) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_83858,plain,(
    ! [D_2297,A_2294,B_2295] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_2297),k1_zfmisc_1(k2_zfmisc_1(A_2294,B_2295)))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_2294,B_2295)))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83669,c_83825])).

tff(c_83880,plain,(
    ! [D_2322,A_2323,B_2324] : m1_subset_1(k7_relat_1('#skF_4',D_2322),k1_zfmisc_1(k2_zfmisc_1(A_2323,B_2324))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_83058,c_83858])).

tff(c_83930,plain,(
    ! [D_2322] : v1_relat_1(k7_relat_1('#skF_4',D_2322)) ),
    inference(resolution,[status(thm)],[c_83880,c_36])).

tff(c_83382,plain,(
    ! [A_2265,B_2266,C_2267,D_2268] :
      ( v1_funct_1(k2_partfun1(A_2265,B_2266,C_2267,D_2268))
      | ~ m1_subset_1(C_2267,k1_zfmisc_1(k2_zfmisc_1(A_2265,B_2266)))
      | ~ v1_funct_1(C_2267) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_83389,plain,(
    ! [A_2265,B_2266,D_2268] :
      ( v1_funct_1(k2_partfun1(A_2265,B_2266,'#skF_4',D_2268))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_83058,c_83382])).

tff(c_83392,plain,(
    ! [A_2265,B_2266,D_2268] : v1_funct_1(k2_partfun1(A_2265,B_2266,'#skF_4',D_2268)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_83389])).

tff(c_83670,plain,(
    ! [D_2268] : v1_funct_1(k7_relat_1('#skF_4',D_2268)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83669,c_83392])).

tff(c_16,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_82204,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82202,c_82202,c_16])).

tff(c_83057,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_83039,c_83039,c_82204])).

tff(c_83555,plain,(
    ! [B_2285,A_2286] :
      ( m1_subset_1(B_2285,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_2285),A_2286)))
      | ~ r1_tarski(k2_relat_1(B_2285),A_2286)
      | ~ v1_funct_1(B_2285)
      | ~ v1_relat_1(B_2285) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_83645,plain,(
    ! [B_2293] :
      ( m1_subset_1(B_2293,k1_zfmisc_1('#skF_4'))
      | ~ r1_tarski(k2_relat_1(B_2293),'#skF_4')
      | ~ v1_funct_1(B_2293)
      | ~ v1_relat_1(B_2293) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83057,c_83555])).

tff(c_83719,plain,(
    ! [B_2307] :
      ( m1_subset_1(B_2307,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(B_2307)
      | ~ v5_relat_1(B_2307,'#skF_4')
      | ~ v1_relat_1(B_2307) ) ),
    inference(resolution,[status(thm)],[c_26,c_83645])).

tff(c_82491,plain,(
    ! [C_2158,A_2159,B_2160] :
      ( v1_xboole_0(C_2158)
      | ~ m1_subset_1(C_2158,k1_zfmisc_1(k2_zfmisc_1(A_2159,B_2160)))
      | ~ v1_xboole_0(A_2159) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_82501,plain,(
    ! [C_2158] :
      ( v1_xboole_0(C_2158)
      | ~ m1_subset_1(C_2158,k1_zfmisc_1('#skF_1'))
      | ~ v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82236,c_82491])).

tff(c_82506,plain,(
    ! [C_2161] :
      ( v1_xboole_0(C_2161)
      | ~ m1_subset_1(C_2161,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82208,c_82501])).

tff(c_82514,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_82237,c_82506])).

tff(c_82520,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_82514,c_82229])).

tff(c_82540,plain,(
    ! [A_7] : m1_subset_1('#skF_4',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82520,c_82245])).

tff(c_82808,plain,(
    ! [A_2190,B_2191,C_2192,D_2193] :
      ( v1_funct_1(k2_partfun1(A_2190,B_2191,C_2192,D_2193))
      | ~ m1_subset_1(C_2192,k1_zfmisc_1(k2_zfmisc_1(A_2190,B_2191)))
      | ~ v1_funct_1(C_2192) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_82815,plain,(
    ! [A_2190,B_2191,D_2193] :
      ( v1_funct_1(k2_partfun1(A_2190,B_2191,'#skF_4',D_2193))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_82540,c_82808])).

tff(c_82818,plain,(
    ! [A_2190,B_2191,D_2193] : v1_funct_1(k2_partfun1(A_2190,B_2191,'#skF_4',D_2193)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_82815])).

tff(c_12,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_82207,plain,(
    ! [A_4] : r1_tarski('#skF_1',A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82202,c_12])).

tff(c_82264,plain,(
    ! [B_2121,A_2122] :
      ( B_2121 = A_2122
      | ~ r1_tarski(B_2121,A_2122)
      | ~ r1_tarski(A_2122,B_2121) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_82270,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_82264])).

tff(c_82278,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82207,c_82270])).

tff(c_82285,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1'))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82278,c_82213,c_82278,c_82278,c_82213,c_82213,c_82278,c_82204,c_82213,c_82213,c_70])).

tff(c_82286,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_82285])).

tff(c_82534,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82520,c_82520,c_82520,c_82286])).

tff(c_82821,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82818,c_82534])).

tff(c_82822,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_82285])).

tff(c_82883,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_82822])).

tff(c_83046,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83039,c_83039,c_83039,c_83039,c_82883])).

tff(c_83671,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83669,c_83046])).

tff(c_83722,plain,
    ( ~ v1_funct_1(k7_relat_1('#skF_4','#skF_4'))
    | ~ v5_relat_1(k7_relat_1('#skF_4','#skF_4'),'#skF_4')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_4')) ),
    inference(resolution,[status(thm)],[c_83719,c_83671])).

tff(c_83750,plain,
    ( ~ v5_relat_1(k7_relat_1('#skF_4','#skF_4'),'#skF_4')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83670,c_83722])).

tff(c_83772,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_83750])).

tff(c_83933,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83930,c_83772])).

tff(c_83934,plain,(
    ~ v5_relat_1(k7_relat_1('#skF_4','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_83750])).

tff(c_84113,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84106,c_83934])).

tff(c_84115,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_82822])).

tff(c_84327,plain,(
    v1_xboole_0(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(resolution,[status(thm)],[c_84115,c_84316])).

tff(c_84553,plain,(
    v1_xboole_0(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84334,c_84334,c_84334,c_84327])).

tff(c_84360,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84334,c_82229])).

tff(c_84557,plain,(
    k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_84553,c_84360])).

tff(c_84114,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_82822])).

tff(c_84347,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84334,c_84334,c_84334,c_84334,c_84334,c_84114])).

tff(c_84627,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84361,c_84557,c_84347])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:48:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 25.82/16.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 25.82/16.13  
% 25.82/16.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 25.82/16.13  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 25.82/16.13  
% 25.82/16.13  %Foreground sorts:
% 25.82/16.13  
% 25.82/16.13  
% 25.82/16.13  %Background operators:
% 25.82/16.13  
% 25.82/16.13  
% 25.82/16.13  %Foreground operators:
% 25.82/16.13  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 25.82/16.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 25.82/16.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 25.82/16.13  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 25.82/16.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 25.82/16.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 25.82/16.13  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 25.82/16.13  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 25.82/16.13  tff('#skF_2', type, '#skF_2': $i).
% 25.82/16.13  tff('#skF_3', type, '#skF_3': $i).
% 25.82/16.13  tff('#skF_1', type, '#skF_1': $i).
% 25.82/16.13  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 25.82/16.13  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 25.82/16.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 25.82/16.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 25.82/16.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 25.82/16.13  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 25.82/16.13  tff('#skF_4', type, '#skF_4': $i).
% 25.82/16.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 25.82/16.13  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 25.82/16.13  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 25.82/16.13  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 25.82/16.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 25.82/16.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 25.82/16.13  
% 25.82/16.16  tff(f_161, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_funct_2)).
% 25.82/16.16  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 25.82/16.16  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 25.82/16.16  tff(f_115, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 25.82/16.16  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 25.82/16.16  tff(f_129, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 25.82/16.16  tff(f_123, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 25.82/16.16  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 25.82/16.16  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 25.82/16.16  tff(f_141, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 25.82/16.16  tff(f_44, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 25.82/16.16  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 25.82/16.16  tff(f_93, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 25.82/16.16  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 25.82/16.16  tff(f_46, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 25.82/16.16  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 25.82/16.16  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 25.82/16.16  tff(c_74, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_161])).
% 25.82/16.16  tff(c_76, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_161])).
% 25.82/16.16  tff(c_128, plain, (![C_51, A_52, B_53]: (v1_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 25.82/16.16  tff(c_140, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_128])).
% 25.82/16.16  tff(c_72, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_161])).
% 25.82/16.16  tff(c_104, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_72])).
% 25.82/16.16  tff(c_78, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_161])).
% 25.82/16.16  tff(c_81445, plain, (![A_2044, B_2045, C_2046]: (k1_relset_1(A_2044, B_2045, C_2046)=k1_relat_1(C_2046) | ~m1_subset_1(C_2046, k1_zfmisc_1(k2_zfmisc_1(A_2044, B_2045))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 25.82/16.16  tff(c_81463, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_81445])).
% 25.82/16.16  tff(c_81773, plain, (![B_2090, A_2091, C_2092]: (k1_xboole_0=B_2090 | k1_relset_1(A_2091, B_2090, C_2092)=A_2091 | ~v1_funct_2(C_2092, A_2091, B_2090) | ~m1_subset_1(C_2092, k1_zfmisc_1(k2_zfmisc_1(A_2091, B_2090))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 25.82/16.16  tff(c_81779, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_76, c_81773])).
% 25.82/16.16  tff(c_81793, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_81463, c_81779])).
% 25.82/16.16  tff(c_81794, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_104, c_81793])).
% 25.82/16.16  tff(c_32, plain, (![B_14, A_13]: (k1_relat_1(k7_relat_1(B_14, A_13))=A_13 | ~r1_tarski(A_13, k1_relat_1(B_14)) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_67])).
% 25.82/16.16  tff(c_81814, plain, (![A_13]: (k1_relat_1(k7_relat_1('#skF_4', A_13))=A_13 | ~r1_tarski(A_13, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_81794, c_32])).
% 25.82/16.16  tff(c_81826, plain, (![A_13]: (k1_relat_1(k7_relat_1('#skF_4', A_13))=A_13 | ~r1_tarski(A_13, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_81814])).
% 25.82/16.16  tff(c_80, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_161])).
% 25.82/16.16  tff(c_81730, plain, (![A_2084, B_2085, C_2086, D_2087]: (k2_partfun1(A_2084, B_2085, C_2086, D_2087)=k7_relat_1(C_2086, D_2087) | ~m1_subset_1(C_2086, k1_zfmisc_1(k2_zfmisc_1(A_2084, B_2085))) | ~v1_funct_1(C_2086))), inference(cnfTransformation, [status(thm)], [f_129])).
% 25.82/16.16  tff(c_81736, plain, (![D_2087]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_2087)=k7_relat_1('#skF_4', D_2087) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_76, c_81730])).
% 25.82/16.16  tff(c_81750, plain, (![D_2087]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_2087)=k7_relat_1('#skF_4', D_2087))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_81736])).
% 25.82/16.16  tff(c_1160, plain, (![A_196, B_197, C_198, D_199]: (k2_partfun1(A_196, B_197, C_198, D_199)=k7_relat_1(C_198, D_199) | ~m1_subset_1(C_198, k1_zfmisc_1(k2_zfmisc_1(A_196, B_197))) | ~v1_funct_1(C_198))), inference(cnfTransformation, [status(thm)], [f_129])).
% 25.82/16.16  tff(c_1164, plain, (![D_199]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_199)=k7_relat_1('#skF_4', D_199) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_76, c_1160])).
% 25.82/16.16  tff(c_1175, plain, (![D_199]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_199)=k7_relat_1('#skF_4', D_199))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1164])).
% 25.82/16.16  tff(c_1529, plain, (![A_223, B_224, C_225, D_226]: (m1_subset_1(k2_partfun1(A_223, B_224, C_225, D_226), k1_zfmisc_1(k2_zfmisc_1(A_223, B_224))) | ~m1_subset_1(C_225, k1_zfmisc_1(k2_zfmisc_1(A_223, B_224))) | ~v1_funct_1(C_225))), inference(cnfTransformation, [status(thm)], [f_123])).
% 25.82/16.16  tff(c_1565, plain, (![D_199]: (m1_subset_1(k7_relat_1('#skF_4', D_199), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1175, c_1529])).
% 25.82/16.16  tff(c_1642, plain, (![D_233]: (m1_subset_1(k7_relat_1('#skF_4', D_233), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_1565])).
% 25.82/16.16  tff(c_36, plain, (![C_20, A_18, B_19]: (v1_relat_1(C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 25.82/16.16  tff(c_1692, plain, (![D_233]: (v1_relat_1(k7_relat_1('#skF_4', D_233)))), inference(resolution, [status(thm)], [c_1642, c_36])).
% 25.82/16.16  tff(c_38, plain, (![C_23, B_22, A_21]: (v5_relat_1(C_23, B_22) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 25.82/16.16  tff(c_1691, plain, (![D_233]: (v5_relat_1(k7_relat_1('#skF_4', D_233), '#skF_2'))), inference(resolution, [status(thm)], [c_1642, c_38])).
% 25.82/16.16  tff(c_26, plain, (![B_12, A_11]: (r1_tarski(k2_relat_1(B_12), A_11) | ~v5_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_58])).
% 25.82/16.16  tff(c_1069, plain, (![A_182, B_183, C_184, D_185]: (v1_funct_1(k2_partfun1(A_182, B_183, C_184, D_185)) | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(A_182, B_183))) | ~v1_funct_1(C_184))), inference(cnfTransformation, [status(thm)], [f_123])).
% 25.82/16.16  tff(c_1071, plain, (![D_185]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_185)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_76, c_1069])).
% 25.82/16.16  tff(c_1081, plain, (![D_185]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_185)))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1071])).
% 25.82/16.16  tff(c_1179, plain, (![D_185]: (v1_funct_1(k7_relat_1('#skF_4', D_185)))), inference(demodulation, [status(thm), theory('equality')], [c_1175, c_1081])).
% 25.82/16.16  tff(c_874, plain, (![A_161, B_162, C_163]: (k1_relset_1(A_161, B_162, C_163)=k1_relat_1(C_163) | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(A_161, B_162))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 25.82/16.16  tff(c_888, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_874])).
% 25.82/16.16  tff(c_1202, plain, (![B_206, A_207, C_208]: (k1_xboole_0=B_206 | k1_relset_1(A_207, B_206, C_208)=A_207 | ~v1_funct_2(C_208, A_207, B_206) | ~m1_subset_1(C_208, k1_zfmisc_1(k2_zfmisc_1(A_207, B_206))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 25.82/16.16  tff(c_1208, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_76, c_1202])).
% 25.82/16.16  tff(c_1222, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_888, c_1208])).
% 25.82/16.16  tff(c_1223, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_104, c_1222])).
% 25.82/16.16  tff(c_1240, plain, (![A_13]: (k1_relat_1(k7_relat_1('#skF_4', A_13))=A_13 | ~r1_tarski(A_13, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1223, c_32])).
% 25.82/16.16  tff(c_1313, plain, (![A_213]: (k1_relat_1(k7_relat_1('#skF_4', A_213))=A_213 | ~r1_tarski(A_213, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_1240])).
% 25.82/16.16  tff(c_64, plain, (![B_43, A_42]: (m1_subset_1(B_43, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_43), A_42))) | ~r1_tarski(k2_relat_1(B_43), A_42) | ~v1_funct_1(B_43) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_141])).
% 25.82/16.16  tff(c_1322, plain, (![A_213, A_42]: (m1_subset_1(k7_relat_1('#skF_4', A_213), k1_zfmisc_1(k2_zfmisc_1(A_213, A_42))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_213)), A_42) | ~v1_funct_1(k7_relat_1('#skF_4', A_213)) | ~v1_relat_1(k7_relat_1('#skF_4', A_213)) | ~r1_tarski(A_213, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1313, c_64])).
% 25.82/16.16  tff(c_1359, plain, (![A_213, A_42]: (m1_subset_1(k7_relat_1('#skF_4', A_213), k1_zfmisc_1(k2_zfmisc_1(A_213, A_42))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_213)), A_42) | ~v1_relat_1(k7_relat_1('#skF_4', A_213)) | ~r1_tarski(A_213, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1179, c_1322])).
% 25.82/16.16  tff(c_80998, plain, (![A_2004, A_2005]: (m1_subset_1(k7_relat_1('#skF_4', A_2004), k1_zfmisc_1(k2_zfmisc_1(A_2004, A_2005))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_2004)), A_2005) | ~r1_tarski(A_2004, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1692, c_1359])).
% 25.82/16.16  tff(c_591, plain, (![A_115, B_116, C_117, D_118]: (v1_funct_1(k2_partfun1(A_115, B_116, C_117, D_118)) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))) | ~v1_funct_1(C_117))), inference(cnfTransformation, [status(thm)], [f_123])).
% 25.82/16.16  tff(c_593, plain, (![D_118]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_118)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_76, c_591])).
% 25.82/16.16  tff(c_603, plain, (![D_118]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_118)))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_593])).
% 25.82/16.16  tff(c_70, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_161])).
% 25.82/16.16  tff(c_142, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_70])).
% 25.82/16.16  tff(c_609, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_603, c_142])).
% 25.82/16.16  tff(c_610, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_70])).
% 25.82/16.16  tff(c_657, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_610])).
% 25.82/16.16  tff(c_1180, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1175, c_657])).
% 25.82/16.16  tff(c_81036, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2') | ~r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_80998, c_1180])).
% 25.82/16.16  tff(c_81110, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_81036])).
% 25.82/16.16  tff(c_81145, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_81110])).
% 25.82/16.16  tff(c_81157, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1692, c_1691, c_81145])).
% 25.82/16.16  tff(c_81159, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_610])).
% 25.82/16.16  tff(c_81462, plain, (k1_relset_1('#skF_3', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_81159, c_81445])).
% 25.82/16.16  tff(c_81756, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_81750, c_81750, c_81462])).
% 25.82/16.16  tff(c_81158, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_610])).
% 25.82/16.16  tff(c_81762, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_81750, c_81158])).
% 25.82/16.16  tff(c_81761, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_81750, c_81159])).
% 25.82/16.16  tff(c_81934, plain, (![B_2100, C_2101, A_2102]: (k1_xboole_0=B_2100 | v1_funct_2(C_2101, A_2102, B_2100) | k1_relset_1(A_2102, B_2100, C_2101)!=A_2102 | ~m1_subset_1(C_2101, k1_zfmisc_1(k2_zfmisc_1(A_2102, B_2100))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 25.82/16.16  tff(c_81937, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_81761, c_81934])).
% 25.82/16.16  tff(c_81956, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_81762, c_104, c_81937])).
% 25.82/16.16  tff(c_82190, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_81756, c_81956])).
% 25.82/16.16  tff(c_82197, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_81826, c_82190])).
% 25.82/16.16  tff(c_82201, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_82197])).
% 25.82/16.16  tff(c_82202, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_72])).
% 25.82/16.16  tff(c_18, plain, (![B_6]: (k2_zfmisc_1(k1_xboole_0, B_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 25.82/16.16  tff(c_82236, plain, (![B_6]: (k2_zfmisc_1('#skF_1', B_6)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82202, c_82202, c_18])).
% 25.82/16.16  tff(c_82203, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_72])).
% 25.82/16.16  tff(c_82213, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_82202, c_82203])).
% 25.82/16.16  tff(c_82228, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_82213, c_76])).
% 25.82/16.16  tff(c_82237, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_82236, c_82228])).
% 25.82/16.16  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 25.82/16.16  tff(c_82208, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82202, c_2])).
% 25.82/16.16  tff(c_84301, plain, (![C_2368, A_2369, B_2370]: (v1_xboole_0(C_2368) | ~m1_subset_1(C_2368, k1_zfmisc_1(k2_zfmisc_1(A_2369, B_2370))) | ~v1_xboole_0(A_2369))), inference(cnfTransformation, [status(thm)], [f_93])).
% 25.82/16.16  tff(c_84311, plain, (![C_2368]: (v1_xboole_0(C_2368) | ~m1_subset_1(C_2368, k1_zfmisc_1('#skF_1')) | ~v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_82236, c_84301])).
% 25.82/16.16  tff(c_84316, plain, (![C_2371]: (v1_xboole_0(C_2371) | ~m1_subset_1(C_2371, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_82208, c_84311])).
% 25.82/16.16  tff(c_84328, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_82237, c_84316])).
% 25.82/16.16  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 25.82/16.16  tff(c_82229, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_82202, c_4])).
% 25.82/16.16  tff(c_84334, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_84328, c_82229])).
% 25.82/16.16  tff(c_82214, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82213, c_78])).
% 25.82/16.16  tff(c_84361, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84334, c_84334, c_82214])).
% 25.82/16.16  tff(c_83010, plain, (![C_2224, A_2225, B_2226]: (v1_xboole_0(C_2224) | ~m1_subset_1(C_2224, k1_zfmisc_1(k2_zfmisc_1(A_2225, B_2226))) | ~v1_xboole_0(A_2225))), inference(cnfTransformation, [status(thm)], [f_93])).
% 25.82/16.16  tff(c_83020, plain, (![C_2224]: (v1_xboole_0(C_2224) | ~m1_subset_1(C_2224, k1_zfmisc_1('#skF_1')) | ~v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_82236, c_83010])).
% 25.82/16.16  tff(c_83025, plain, (![C_2227]: (v1_xboole_0(C_2227) | ~m1_subset_1(C_2227, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_82208, c_83020])).
% 25.82/16.16  tff(c_83033, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_82237, c_83025])).
% 25.82/16.16  tff(c_83039, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_83033, c_82229])).
% 25.82/16.16  tff(c_20, plain, (![A_7]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 25.82/16.16  tff(c_82245, plain, (![A_7]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_82202, c_20])).
% 25.82/16.16  tff(c_83058, plain, (![A_7]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_83039, c_82245])).
% 25.82/16.16  tff(c_83656, plain, (![A_2294, B_2295, C_2296, D_2297]: (k2_partfun1(A_2294, B_2295, C_2296, D_2297)=k7_relat_1(C_2296, D_2297) | ~m1_subset_1(C_2296, k1_zfmisc_1(k2_zfmisc_1(A_2294, B_2295))) | ~v1_funct_1(C_2296))), inference(cnfTransformation, [status(thm)], [f_129])).
% 25.82/16.16  tff(c_83665, plain, (![A_2294, B_2295, D_2297]: (k2_partfun1(A_2294, B_2295, '#skF_4', D_2297)=k7_relat_1('#skF_4', D_2297) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_83058, c_83656])).
% 25.82/16.16  tff(c_83669, plain, (![A_2294, B_2295, D_2297]: (k2_partfun1(A_2294, B_2295, '#skF_4', D_2297)=k7_relat_1('#skF_4', D_2297))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_83665])).
% 25.82/16.16  tff(c_84002, plain, (![A_2336, B_2337, C_2338, D_2339]: (m1_subset_1(k2_partfun1(A_2336, B_2337, C_2338, D_2339), k1_zfmisc_1(k2_zfmisc_1(A_2336, B_2337))) | ~m1_subset_1(C_2338, k1_zfmisc_1(k2_zfmisc_1(A_2336, B_2337))) | ~v1_funct_1(C_2338))), inference(cnfTransformation, [status(thm)], [f_123])).
% 25.82/16.16  tff(c_84035, plain, (![D_2297, A_2294, B_2295]: (m1_subset_1(k7_relat_1('#skF_4', D_2297), k1_zfmisc_1(k2_zfmisc_1(A_2294, B_2295))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_2294, B_2295))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_83669, c_84002])).
% 25.82/16.16  tff(c_84057, plain, (![D_2340, A_2341, B_2342]: (m1_subset_1(k7_relat_1('#skF_4', D_2340), k1_zfmisc_1(k2_zfmisc_1(A_2341, B_2342))))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_83058, c_84035])).
% 25.82/16.16  tff(c_84106, plain, (![D_2340, B_2342]: (v5_relat_1(k7_relat_1('#skF_4', D_2340), B_2342))), inference(resolution, [status(thm)], [c_84057, c_38])).
% 25.82/16.16  tff(c_83825, plain, (![A_2318, B_2319, C_2320, D_2321]: (m1_subset_1(k2_partfun1(A_2318, B_2319, C_2320, D_2321), k1_zfmisc_1(k2_zfmisc_1(A_2318, B_2319))) | ~m1_subset_1(C_2320, k1_zfmisc_1(k2_zfmisc_1(A_2318, B_2319))) | ~v1_funct_1(C_2320))), inference(cnfTransformation, [status(thm)], [f_123])).
% 25.82/16.16  tff(c_83858, plain, (![D_2297, A_2294, B_2295]: (m1_subset_1(k7_relat_1('#skF_4', D_2297), k1_zfmisc_1(k2_zfmisc_1(A_2294, B_2295))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_2294, B_2295))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_83669, c_83825])).
% 25.82/16.16  tff(c_83880, plain, (![D_2322, A_2323, B_2324]: (m1_subset_1(k7_relat_1('#skF_4', D_2322), k1_zfmisc_1(k2_zfmisc_1(A_2323, B_2324))))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_83058, c_83858])).
% 25.82/16.16  tff(c_83930, plain, (![D_2322]: (v1_relat_1(k7_relat_1('#skF_4', D_2322)))), inference(resolution, [status(thm)], [c_83880, c_36])).
% 25.82/16.16  tff(c_83382, plain, (![A_2265, B_2266, C_2267, D_2268]: (v1_funct_1(k2_partfun1(A_2265, B_2266, C_2267, D_2268)) | ~m1_subset_1(C_2267, k1_zfmisc_1(k2_zfmisc_1(A_2265, B_2266))) | ~v1_funct_1(C_2267))), inference(cnfTransformation, [status(thm)], [f_123])).
% 25.82/16.16  tff(c_83389, plain, (![A_2265, B_2266, D_2268]: (v1_funct_1(k2_partfun1(A_2265, B_2266, '#skF_4', D_2268)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_83058, c_83382])).
% 25.82/16.16  tff(c_83392, plain, (![A_2265, B_2266, D_2268]: (v1_funct_1(k2_partfun1(A_2265, B_2266, '#skF_4', D_2268)))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_83389])).
% 25.82/16.16  tff(c_83670, plain, (![D_2268]: (v1_funct_1(k7_relat_1('#skF_4', D_2268)))), inference(demodulation, [status(thm), theory('equality')], [c_83669, c_83392])).
% 25.82/16.16  tff(c_16, plain, (![A_5]: (k2_zfmisc_1(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 25.82/16.16  tff(c_82204, plain, (![A_5]: (k2_zfmisc_1(A_5, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82202, c_82202, c_16])).
% 25.82/16.16  tff(c_83057, plain, (![A_5]: (k2_zfmisc_1(A_5, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_83039, c_83039, c_82204])).
% 25.82/16.16  tff(c_83555, plain, (![B_2285, A_2286]: (m1_subset_1(B_2285, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_2285), A_2286))) | ~r1_tarski(k2_relat_1(B_2285), A_2286) | ~v1_funct_1(B_2285) | ~v1_relat_1(B_2285))), inference(cnfTransformation, [status(thm)], [f_141])).
% 25.82/16.16  tff(c_83645, plain, (![B_2293]: (m1_subset_1(B_2293, k1_zfmisc_1('#skF_4')) | ~r1_tarski(k2_relat_1(B_2293), '#skF_4') | ~v1_funct_1(B_2293) | ~v1_relat_1(B_2293))), inference(superposition, [status(thm), theory('equality')], [c_83057, c_83555])).
% 25.82/16.16  tff(c_83719, plain, (![B_2307]: (m1_subset_1(B_2307, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(B_2307) | ~v5_relat_1(B_2307, '#skF_4') | ~v1_relat_1(B_2307))), inference(resolution, [status(thm)], [c_26, c_83645])).
% 25.82/16.16  tff(c_82491, plain, (![C_2158, A_2159, B_2160]: (v1_xboole_0(C_2158) | ~m1_subset_1(C_2158, k1_zfmisc_1(k2_zfmisc_1(A_2159, B_2160))) | ~v1_xboole_0(A_2159))), inference(cnfTransformation, [status(thm)], [f_93])).
% 25.82/16.16  tff(c_82501, plain, (![C_2158]: (v1_xboole_0(C_2158) | ~m1_subset_1(C_2158, k1_zfmisc_1('#skF_1')) | ~v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_82236, c_82491])).
% 25.82/16.16  tff(c_82506, plain, (![C_2161]: (v1_xboole_0(C_2161) | ~m1_subset_1(C_2161, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_82208, c_82501])).
% 25.82/16.16  tff(c_82514, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_82237, c_82506])).
% 25.82/16.16  tff(c_82520, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_82514, c_82229])).
% 25.82/16.16  tff(c_82540, plain, (![A_7]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_82520, c_82245])).
% 25.82/16.16  tff(c_82808, plain, (![A_2190, B_2191, C_2192, D_2193]: (v1_funct_1(k2_partfun1(A_2190, B_2191, C_2192, D_2193)) | ~m1_subset_1(C_2192, k1_zfmisc_1(k2_zfmisc_1(A_2190, B_2191))) | ~v1_funct_1(C_2192))), inference(cnfTransformation, [status(thm)], [f_123])).
% 25.82/16.16  tff(c_82815, plain, (![A_2190, B_2191, D_2193]: (v1_funct_1(k2_partfun1(A_2190, B_2191, '#skF_4', D_2193)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_82540, c_82808])).
% 25.82/16.16  tff(c_82818, plain, (![A_2190, B_2191, D_2193]: (v1_funct_1(k2_partfun1(A_2190, B_2191, '#skF_4', D_2193)))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_82815])).
% 25.82/16.16  tff(c_12, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 25.82/16.16  tff(c_82207, plain, (![A_4]: (r1_tarski('#skF_1', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_82202, c_12])).
% 25.82/16.16  tff(c_82264, plain, (![B_2121, A_2122]: (B_2121=A_2122 | ~r1_tarski(B_2121, A_2122) | ~r1_tarski(A_2122, B_2121))), inference(cnfTransformation, [status(thm)], [f_36])).
% 25.82/16.16  tff(c_82270, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_74, c_82264])).
% 25.82/16.16  tff(c_82278, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_82207, c_82270])).
% 25.82/16.16  tff(c_82285, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1')) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_82278, c_82213, c_82278, c_82278, c_82213, c_82213, c_82278, c_82204, c_82213, c_82213, c_70])).
% 25.82/16.16  tff(c_82286, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(splitLeft, [status(thm)], [c_82285])).
% 25.82/16.16  tff(c_82534, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_82520, c_82520, c_82520, c_82286])).
% 25.82/16.16  tff(c_82821, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82818, c_82534])).
% 25.82/16.16  tff(c_82822, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_82285])).
% 25.82/16.16  tff(c_82883, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_82822])).
% 25.82/16.16  tff(c_83046, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_83039, c_83039, c_83039, c_83039, c_82883])).
% 25.82/16.16  tff(c_83671, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_83669, c_83046])).
% 25.82/16.16  tff(c_83722, plain, (~v1_funct_1(k7_relat_1('#skF_4', '#skF_4')) | ~v5_relat_1(k7_relat_1('#skF_4', '#skF_4'), '#skF_4') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_83719, c_83671])).
% 25.82/16.16  tff(c_83750, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_4'), '#skF_4') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_83670, c_83722])).
% 25.82/16.16  tff(c_83772, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_4'))), inference(splitLeft, [status(thm)], [c_83750])).
% 25.82/16.16  tff(c_83933, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83930, c_83772])).
% 25.82/16.16  tff(c_83934, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_83750])).
% 25.82/16.16  tff(c_84113, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84106, c_83934])).
% 25.82/16.16  tff(c_84115, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_82822])).
% 25.82/16.16  tff(c_84327, plain, (v1_xboole_0(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(resolution, [status(thm)], [c_84115, c_84316])).
% 25.82/16.16  tff(c_84553, plain, (v1_xboole_0(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_84334, c_84334, c_84334, c_84327])).
% 25.82/16.16  tff(c_84360, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_84334, c_82229])).
% 25.82/16.16  tff(c_84557, plain, (k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_84553, c_84360])).
% 25.82/16.16  tff(c_84114, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_82822])).
% 25.82/16.16  tff(c_84347, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84334, c_84334, c_84334, c_84334, c_84334, c_84114])).
% 25.82/16.16  tff(c_84627, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84361, c_84557, c_84347])).
% 25.82/16.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 25.82/16.16  
% 25.82/16.16  Inference rules
% 25.82/16.16  ----------------------
% 25.82/16.16  #Ref     : 0
% 25.82/16.16  #Sup     : 17275
% 25.82/16.16  #Fact    : 0
% 25.82/16.16  #Define  : 0
% 25.82/16.16  #Split   : 38
% 25.82/16.16  #Chain   : 0
% 25.82/16.16  #Close   : 0
% 25.82/16.16  
% 25.82/16.16  Ordering : KBO
% 25.82/16.16  
% 25.82/16.16  Simplification rules
% 25.82/16.16  ----------------------
% 25.82/16.16  #Subsume      : 5045
% 25.82/16.16  #Demod        : 40460
% 25.82/16.16  #Tautology    : 7172
% 25.82/16.16  #SimpNegUnit  : 285
% 25.82/16.16  #BackRed      : 215
% 25.82/16.16  
% 25.82/16.16  #Partial instantiations: 0
% 25.82/16.16  #Strategies tried      : 1
% 25.82/16.16  
% 25.82/16.16  Timing (in seconds)
% 25.82/16.16  ----------------------
% 25.82/16.16  Preprocessing        : 0.36
% 25.82/16.16  Parsing              : 0.20
% 25.82/16.16  CNF conversion       : 0.02
% 25.82/16.16  Main loop            : 14.96
% 25.82/16.16  Inferencing          : 2.69
% 25.82/16.16  Reduction            : 6.73
% 25.82/16.16  Demodulation         : 5.61
% 25.82/16.16  BG Simplification    : 0.21
% 25.82/16.16  Subsumption          : 4.64
% 25.82/16.16  Abstraction          : 0.43
% 25.82/16.16  MUC search           : 0.00
% 25.82/16.16  Cooper               : 0.00
% 25.82/16.16  Total                : 15.38
% 25.82/16.16  Index Insertion      : 0.00
% 25.82/16.16  Index Deletion       : 0.00
% 25.82/16.16  Index Matching       : 0.00
% 25.82/16.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
