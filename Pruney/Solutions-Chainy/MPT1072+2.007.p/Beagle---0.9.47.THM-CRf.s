%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:56 EST 2020

% Result     : Theorem 3.95s
% Output     : CNFRefutation 3.95s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 214 expanded)
%              Number of leaves         :   45 (  99 expanded)
%              Depth                    :   11
%              Number of atoms          :  129 ( 524 expanded)
%              Number of equality atoms :   36 ( 101 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k3_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_partfun1,type,(
    k7_partfun1: ( $i * $i * $i ) > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_203,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,A)
               => ! [D] :
                    ( ( v1_funct_1(D)
                      & v1_funct_2(D,A,B)
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
                   => r2_hidden(k3_funct_2(A,B,D,C),k2_relset_1(A,B,D)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_funct_2)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_90,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_127,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_123,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_133,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_119,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_139,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( k7_relset_1(B,A,C,k8_relset_1(B,A,C,A)) = k2_relset_1(B,A,C)
        & k8_relset_1(B,A,C,k7_relset_1(B,A,C,B)) = k1_relset_1(B,A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).

tff(f_183,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => k8_relset_1(A,B,C,k7_relset_1(A,B,C,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_funct_2)).

tff(f_115,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_152,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_88,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_90,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_86,plain,(
    m1_subset_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_26,plain,(
    ! [B_16,A_15] :
      ( r2_hidden(B_16,A_15)
      | ~ m1_subset_1(B_16,A_15)
      | v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_38,plain,(
    ! [A_22,B_23] : v1_relat_1(k2_zfmisc_1(A_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_80,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_212,plain,(
    ! [B_102,A_103] :
      ( v1_relat_1(B_102)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(A_103))
      | ~ v1_relat_1(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_219,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_80,c_212])).

tff(c_223,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_219])).

tff(c_84,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_82,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_648,plain,(
    ! [A_142,B_143,C_144,D_145] :
      ( k7_relset_1(A_142,B_143,C_144,D_145) = k9_relat_1(C_144,D_145)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(A_142,B_143))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_655,plain,(
    ! [D_145] : k7_relset_1('#skF_1','#skF_2','#skF_4',D_145) = k9_relat_1('#skF_4',D_145) ),
    inference(resolution,[status(thm)],[c_80,c_648])).

tff(c_625,plain,(
    ! [A_139,B_140,C_141] :
      ( k2_relset_1(A_139,B_140,C_141) = k2_relat_1(C_141)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_634,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_625])).

tff(c_782,plain,(
    ! [A_166,B_167,C_168] :
      ( k7_relset_1(A_166,B_167,C_168,A_166) = k2_relset_1(A_166,B_167,C_168)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(A_166,B_167))) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_787,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_4','#skF_1') = k2_relset_1('#skF_1','#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_782])).

tff(c_790,plain,(
    k9_relat_1('#skF_4','#skF_1') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_655,c_634,c_787])).

tff(c_502,plain,(
    ! [A_132,B_133,C_134] :
      ( k1_relset_1(A_132,B_133,C_134) = k1_relat_1(C_134)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(A_132,B_133))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_511,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_502])).

tff(c_930,plain,(
    ! [B_193,A_194,C_195] :
      ( k8_relset_1(B_193,A_194,C_195,k7_relset_1(B_193,A_194,C_195,B_193)) = k1_relset_1(B_193,A_194,C_195)
      | ~ m1_subset_1(C_195,k1_zfmisc_1(k2_zfmisc_1(B_193,A_194))) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_935,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_4',k7_relset_1('#skF_1','#skF_2','#skF_4','#skF_1')) = k1_relset_1('#skF_1','#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_930])).

tff(c_938,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_4',k2_relat_1('#skF_4')) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_790,c_655,c_511,c_935])).

tff(c_1009,plain,(
    ! [B_215,A_216,C_217] :
      ( k1_xboole_0 = B_215
      | k8_relset_1(A_216,B_215,C_217,k7_relset_1(A_216,B_215,C_217,A_216)) = A_216
      | ~ m1_subset_1(C_217,k1_zfmisc_1(k2_zfmisc_1(A_216,B_215)))
      | ~ v1_funct_2(C_217,A_216,B_215)
      | ~ v1_funct_1(C_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_1014,plain,
    ( k1_xboole_0 = '#skF_2'
    | k8_relset_1('#skF_1','#skF_2','#skF_4',k7_relset_1('#skF_1','#skF_2','#skF_4','#skF_1')) = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_1009])).

tff(c_1018,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_938,c_790,c_655,c_1014])).

tff(c_1019,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1018])).

tff(c_54,plain,(
    ! [B_29,A_28] :
      ( r2_hidden(k1_funct_1(B_29,A_28),k2_relat_1(B_29))
      | ~ r2_hidden(A_28,k1_relat_1(B_29))
      | ~ v1_funct_1(B_29)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1104,plain,(
    ! [A_220,B_221,C_222,D_223] :
      ( k3_funct_2(A_220,B_221,C_222,D_223) = k1_funct_1(C_222,D_223)
      | ~ m1_subset_1(D_223,A_220)
      | ~ m1_subset_1(C_222,k1_zfmisc_1(k2_zfmisc_1(A_220,B_221)))
      | ~ v1_funct_2(C_222,A_220,B_221)
      | ~ v1_funct_1(C_222)
      | v1_xboole_0(A_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_1110,plain,(
    ! [B_221,C_222] :
      ( k3_funct_2('#skF_1',B_221,C_222,'#skF_3') = k1_funct_1(C_222,'#skF_3')
      | ~ m1_subset_1(C_222,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_221)))
      | ~ v1_funct_2(C_222,'#skF_1',B_221)
      | ~ v1_funct_1(C_222)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_86,c_1104])).

tff(c_1239,plain,(
    ! [B_234,C_235] :
      ( k3_funct_2('#skF_1',B_234,C_235,'#skF_3') = k1_funct_1(C_235,'#skF_3')
      | ~ m1_subset_1(C_235,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_234)))
      | ~ v1_funct_2(C_235,'#skF_1',B_234)
      | ~ v1_funct_1(C_235) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_1110])).

tff(c_1246,plain,
    ( k3_funct_2('#skF_1','#skF_2','#skF_4','#skF_3') = k1_funct_1('#skF_4','#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_1239])).

tff(c_1250,plain,(
    k3_funct_2('#skF_1','#skF_2','#skF_4','#skF_3') = k1_funct_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_1246])).

tff(c_78,plain,(
    ~ r2_hidden(k3_funct_2('#skF_1','#skF_2','#skF_4','#skF_3'),k2_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_637,plain,(
    ~ r2_hidden(k3_funct_2('#skF_1','#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_634,c_78])).

tff(c_1252,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1250,c_637])).

tff(c_1259,plain,
    ( ~ r2_hidden('#skF_3',k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_1252])).

tff(c_1265,plain,(
    ~ r2_hidden('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_84,c_1019,c_1259])).

tff(c_1271,plain,
    ( ~ m1_subset_1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_1265])).

tff(c_1274,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1271])).

tff(c_1276,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_1274])).

tff(c_1277,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1018])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1324,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1277,c_2])).

tff(c_1326,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_1324])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:53:31 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.95/1.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.95/1.72  
% 3.95/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.95/1.72  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k3_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.95/1.72  
% 3.95/1.72  %Foreground sorts:
% 3.95/1.72  
% 3.95/1.72  
% 3.95/1.72  %Background operators:
% 3.95/1.72  
% 3.95/1.72  
% 3.95/1.72  %Foreground operators:
% 3.95/1.72  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.95/1.72  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.95/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.95/1.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.95/1.72  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.95/1.72  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.95/1.72  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.95/1.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.95/1.72  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.95/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.95/1.72  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.95/1.72  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 3.95/1.72  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.95/1.72  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.95/1.72  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.95/1.72  tff('#skF_2', type, '#skF_2': $i).
% 3.95/1.72  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.95/1.72  tff('#skF_3', type, '#skF_3': $i).
% 3.95/1.72  tff('#skF_1', type, '#skF_1': $i).
% 3.95/1.72  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.95/1.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.95/1.72  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.95/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.95/1.72  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.95/1.72  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.95/1.72  tff('#skF_4', type, '#skF_4': $i).
% 3.95/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.95/1.72  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.95/1.72  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.95/1.72  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 3.95/1.72  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.95/1.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.95/1.72  
% 3.95/1.74  tff(f_203, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, A) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_hidden(k3_funct_2(A, B, D, C), k2_relset_1(A, B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t189_funct_2)).
% 3.95/1.74  tff(f_73, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.95/1.74  tff(f_90, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.95/1.74  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.95/1.74  tff(f_127, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.95/1.74  tff(f_123, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.95/1.74  tff(f_133, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 3.95/1.74  tff(f_119, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.95/1.74  tff(f_139, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_relset_1)).
% 3.95/1.74  tff(f_183, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, k7_relset_1(A, B, C, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_funct_2)).
% 3.95/1.74  tff(f_115, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 3.95/1.74  tff(f_152, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 3.95/1.74  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.95/1.74  tff(c_88, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_203])).
% 3.95/1.74  tff(c_90, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_203])).
% 3.95/1.74  tff(c_86, plain, (m1_subset_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_203])).
% 3.95/1.74  tff(c_26, plain, (![B_16, A_15]: (r2_hidden(B_16, A_15) | ~m1_subset_1(B_16, A_15) | v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.95/1.74  tff(c_38, plain, (![A_22, B_23]: (v1_relat_1(k2_zfmisc_1(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.95/1.74  tff(c_80, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_203])).
% 3.95/1.74  tff(c_212, plain, (![B_102, A_103]: (v1_relat_1(B_102) | ~m1_subset_1(B_102, k1_zfmisc_1(A_103)) | ~v1_relat_1(A_103))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.95/1.74  tff(c_219, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_80, c_212])).
% 3.95/1.74  tff(c_223, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_219])).
% 3.95/1.74  tff(c_84, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_203])).
% 3.95/1.74  tff(c_82, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_203])).
% 3.95/1.74  tff(c_648, plain, (![A_142, B_143, C_144, D_145]: (k7_relset_1(A_142, B_143, C_144, D_145)=k9_relat_1(C_144, D_145) | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(A_142, B_143))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.95/1.74  tff(c_655, plain, (![D_145]: (k7_relset_1('#skF_1', '#skF_2', '#skF_4', D_145)=k9_relat_1('#skF_4', D_145))), inference(resolution, [status(thm)], [c_80, c_648])).
% 3.95/1.74  tff(c_625, plain, (![A_139, B_140, C_141]: (k2_relset_1(A_139, B_140, C_141)=k2_relat_1(C_141) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.95/1.74  tff(c_634, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_80, c_625])).
% 3.95/1.74  tff(c_782, plain, (![A_166, B_167, C_168]: (k7_relset_1(A_166, B_167, C_168, A_166)=k2_relset_1(A_166, B_167, C_168) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.95/1.74  tff(c_787, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_1')=k2_relset_1('#skF_1', '#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_80, c_782])).
% 3.95/1.74  tff(c_790, plain, (k9_relat_1('#skF_4', '#skF_1')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_655, c_634, c_787])).
% 3.95/1.74  tff(c_502, plain, (![A_132, B_133, C_134]: (k1_relset_1(A_132, B_133, C_134)=k1_relat_1(C_134) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(A_132, B_133))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.95/1.74  tff(c_511, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_80, c_502])).
% 3.95/1.74  tff(c_930, plain, (![B_193, A_194, C_195]: (k8_relset_1(B_193, A_194, C_195, k7_relset_1(B_193, A_194, C_195, B_193))=k1_relset_1(B_193, A_194, C_195) | ~m1_subset_1(C_195, k1_zfmisc_1(k2_zfmisc_1(B_193, A_194))))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.95/1.74  tff(c_935, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_4', k7_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_1'))=k1_relset_1('#skF_1', '#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_80, c_930])).
% 3.95/1.74  tff(c_938, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_4', k2_relat_1('#skF_4'))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_790, c_655, c_511, c_935])).
% 3.95/1.74  tff(c_1009, plain, (![B_215, A_216, C_217]: (k1_xboole_0=B_215 | k8_relset_1(A_216, B_215, C_217, k7_relset_1(A_216, B_215, C_217, A_216))=A_216 | ~m1_subset_1(C_217, k1_zfmisc_1(k2_zfmisc_1(A_216, B_215))) | ~v1_funct_2(C_217, A_216, B_215) | ~v1_funct_1(C_217))), inference(cnfTransformation, [status(thm)], [f_183])).
% 3.95/1.74  tff(c_1014, plain, (k1_xboole_0='#skF_2' | k8_relset_1('#skF_1', '#skF_2', '#skF_4', k7_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_1'))='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_80, c_1009])).
% 3.95/1.74  tff(c_1018, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_938, c_790, c_655, c_1014])).
% 3.95/1.74  tff(c_1019, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(splitLeft, [status(thm)], [c_1018])).
% 3.95/1.74  tff(c_54, plain, (![B_29, A_28]: (r2_hidden(k1_funct_1(B_29, A_28), k2_relat_1(B_29)) | ~r2_hidden(A_28, k1_relat_1(B_29)) | ~v1_funct_1(B_29) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.95/1.74  tff(c_1104, plain, (![A_220, B_221, C_222, D_223]: (k3_funct_2(A_220, B_221, C_222, D_223)=k1_funct_1(C_222, D_223) | ~m1_subset_1(D_223, A_220) | ~m1_subset_1(C_222, k1_zfmisc_1(k2_zfmisc_1(A_220, B_221))) | ~v1_funct_2(C_222, A_220, B_221) | ~v1_funct_1(C_222) | v1_xboole_0(A_220))), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.95/1.74  tff(c_1110, plain, (![B_221, C_222]: (k3_funct_2('#skF_1', B_221, C_222, '#skF_3')=k1_funct_1(C_222, '#skF_3') | ~m1_subset_1(C_222, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_221))) | ~v1_funct_2(C_222, '#skF_1', B_221) | ~v1_funct_1(C_222) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_86, c_1104])).
% 3.95/1.74  tff(c_1239, plain, (![B_234, C_235]: (k3_funct_2('#skF_1', B_234, C_235, '#skF_3')=k1_funct_1(C_235, '#skF_3') | ~m1_subset_1(C_235, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_234))) | ~v1_funct_2(C_235, '#skF_1', B_234) | ~v1_funct_1(C_235))), inference(negUnitSimplification, [status(thm)], [c_90, c_1110])).
% 3.95/1.74  tff(c_1246, plain, (k3_funct_2('#skF_1', '#skF_2', '#skF_4', '#skF_3')=k1_funct_1('#skF_4', '#skF_3') | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_80, c_1239])).
% 3.95/1.74  tff(c_1250, plain, (k3_funct_2('#skF_1', '#skF_2', '#skF_4', '#skF_3')=k1_funct_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_1246])).
% 3.95/1.74  tff(c_78, plain, (~r2_hidden(k3_funct_2('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k2_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_203])).
% 3.95/1.74  tff(c_637, plain, (~r2_hidden(k3_funct_2('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_634, c_78])).
% 3.95/1.74  tff(c_1252, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1250, c_637])).
% 3.95/1.74  tff(c_1259, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_1252])).
% 3.95/1.74  tff(c_1265, plain, (~r2_hidden('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_223, c_84, c_1019, c_1259])).
% 3.95/1.74  tff(c_1271, plain, (~m1_subset_1('#skF_3', '#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_26, c_1265])).
% 3.95/1.74  tff(c_1274, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1271])).
% 3.95/1.74  tff(c_1276, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_1274])).
% 3.95/1.74  tff(c_1277, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_1018])).
% 3.95/1.74  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.95/1.74  tff(c_1324, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1277, c_2])).
% 3.95/1.74  tff(c_1326, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_1324])).
% 3.95/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.95/1.74  
% 3.95/1.74  Inference rules
% 3.95/1.74  ----------------------
% 3.95/1.74  #Ref     : 4
% 3.95/1.74  #Sup     : 257
% 3.95/1.74  #Fact    : 0
% 3.95/1.74  #Define  : 0
% 3.95/1.74  #Split   : 7
% 3.95/1.74  #Chain   : 0
% 3.95/1.74  #Close   : 0
% 3.95/1.74  
% 3.95/1.74  Ordering : KBO
% 3.95/1.74  
% 3.95/1.74  Simplification rules
% 3.95/1.74  ----------------------
% 3.95/1.74  #Subsume      : 20
% 3.95/1.74  #Demod        : 292
% 3.95/1.74  #Tautology    : 152
% 3.95/1.74  #SimpNegUnit  : 13
% 3.95/1.74  #BackRed      : 55
% 3.95/1.74  
% 3.95/1.74  #Partial instantiations: 0
% 3.95/1.74  #Strategies tried      : 1
% 3.95/1.74  
% 3.95/1.74  Timing (in seconds)
% 3.95/1.74  ----------------------
% 3.95/1.74  Preprocessing        : 0.46
% 3.95/1.74  Parsing              : 0.24
% 3.95/1.74  CNF conversion       : 0.03
% 3.95/1.74  Main loop            : 0.48
% 3.95/1.74  Inferencing          : 0.16
% 3.95/1.74  Reduction            : 0.16
% 3.95/1.74  Demodulation         : 0.12
% 3.95/1.74  BG Simplification    : 0.03
% 3.95/1.74  Subsumption          : 0.09
% 3.95/1.74  Abstraction          : 0.03
% 3.95/1.74  MUC search           : 0.00
% 3.95/1.74  Cooper               : 0.00
% 3.95/1.74  Total                : 0.97
% 3.95/1.74  Index Insertion      : 0.00
% 3.95/1.74  Index Deletion       : 0.00
% 3.95/1.74  Index Matching       : 0.00
% 3.95/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
