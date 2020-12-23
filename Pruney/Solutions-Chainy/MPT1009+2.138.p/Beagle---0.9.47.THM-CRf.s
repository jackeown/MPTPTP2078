%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:01 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 260 expanded)
%              Number of leaves         :   50 ( 109 expanded)
%              Depth                    :   14
%              Number of atoms          :  148 ( 487 expanded)
%              Number of equality atoms :   40 ( 110 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_85,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_132,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_97,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_120,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_116,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_44,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_110,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_42,plain,(
    ! [A_44,B_45] : v1_relat_1(k2_zfmisc_1(A_44,B_45)) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_64,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_6'),'#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_229,plain,(
    ! [B_86,A_87] :
      ( v1_relat_1(B_86)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(A_87))
      | ~ v1_relat_1(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_232,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_6'),'#skF_7')) ),
    inference(resolution,[status(thm)],[c_64,c_229])).

tff(c_235,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_232])).

tff(c_44,plain,(
    ! [B_47,A_46] :
      ( r1_tarski(k9_relat_1(B_47,A_46),k2_relat_1(B_47))
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_48,plain,(
    ! [A_48] :
      ( k1_relat_1(A_48) != k1_xboole_0
      | k1_xboole_0 = A_48
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_242,plain,
    ( k1_relat_1('#skF_9') != k1_xboole_0
    | k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_235,c_48])).

tff(c_244,plain,(
    k1_relat_1('#skF_9') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_242])).

tff(c_68,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_50,plain,(
    ! [B_50,A_49] :
      ( k1_tarski(k1_funct_1(B_50,A_49)) = k2_relat_1(B_50)
      | k1_tarski(A_49) != k1_relat_1(B_50)
      | ~ v1_funct_1(B_50)
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_484,plain,(
    ! [A_132,B_133,C_134,D_135] :
      ( k7_relset_1(A_132,B_133,C_134,D_135) = k9_relat_1(C_134,D_135)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(A_132,B_133))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_487,plain,(
    ! [D_135] : k7_relset_1(k1_tarski('#skF_6'),'#skF_7','#skF_9',D_135) = k9_relat_1('#skF_9',D_135) ),
    inference(resolution,[status(thm)],[c_64,c_484])).

tff(c_60,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_6'),'#skF_7','#skF_9','#skF_8'),k1_tarski(k1_funct_1('#skF_9','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_522,plain,(
    ~ r1_tarski(k9_relat_1('#skF_9','#skF_8'),k1_tarski(k1_funct_1('#skF_9','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_487,c_60])).

tff(c_546,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_9','#skF_8'),k2_relat_1('#skF_9'))
    | k1_tarski('#skF_6') != k1_relat_1('#skF_9')
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_522])).

tff(c_551,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_9','#skF_8'),k2_relat_1('#skF_9'))
    | k1_tarski('#skF_6') != k1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_68,c_546])).

tff(c_555,plain,(
    k1_tarski('#skF_6') != k1_relat_1('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_551])).

tff(c_318,plain,(
    ! [C_102,A_103,B_104] :
      ( v4_relat_1(C_102,A_103)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_322,plain,(
    v4_relat_1('#skF_9',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_64,c_318])).

tff(c_349,plain,(
    ! [B_113,A_114] :
      ( r1_tarski(k1_relat_1(B_113),A_114)
      | ~ v4_relat_1(B_113,A_114)
      | ~ v1_relat_1(B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_22,plain,(
    ! [B_19,A_18] :
      ( k1_tarski(B_19) = A_18
      | k1_xboole_0 = A_18
      | ~ r1_tarski(A_18,k1_tarski(B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_871,plain,(
    ! [B_182,B_183] :
      ( k1_tarski(B_182) = k1_relat_1(B_183)
      | k1_relat_1(B_183) = k1_xboole_0
      | ~ v4_relat_1(B_183,k1_tarski(B_182))
      | ~ v1_relat_1(B_183) ) ),
    inference(resolution,[status(thm)],[c_349,c_22])).

tff(c_877,plain,
    ( k1_tarski('#skF_6') = k1_relat_1('#skF_9')
    | k1_relat_1('#skF_9') = k1_xboole_0
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_322,c_871])).

tff(c_880,plain,
    ( k1_tarski('#skF_6') = k1_relat_1('#skF_9')
    | k1_relat_1('#skF_9') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_877])).

tff(c_882,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_244,c_555,c_880])).

tff(c_883,plain,(
    ~ r1_tarski(k9_relat_1('#skF_9','#skF_8'),k2_relat_1('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_551])).

tff(c_918,plain,(
    ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_44,c_883])).

tff(c_925,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_918])).

tff(c_926,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_242])).

tff(c_14,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_110,plain,(
    ! [B_74,A_75] :
      ( ~ r1_tarski(B_74,A_75)
      | ~ r2_hidden(A_75,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_119,plain,(
    ! [A_76] :
      ( ~ r1_tarski(A_76,'#skF_1'(A_76))
      | v1_xboole_0(A_76) ) ),
    inference(resolution,[status(thm)],[c_4,c_110])).

tff(c_124,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_119])).

tff(c_933,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_926,c_124])).

tff(c_73,plain,(
    ! [A_64] :
      ( v1_xboole_0(k2_relat_1(A_64))
      | ~ v1_xboole_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_12,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_77,plain,(
    ! [A_64] :
      ( k2_relat_1(A_64) = k1_xboole_0
      | ~ v1_xboole_0(A_64) ) ),
    inference(resolution,[status(thm)],[c_73,c_12])).

tff(c_135,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_124,c_77])).

tff(c_931,plain,(
    k2_relat_1('#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_926,c_926,c_135])).

tff(c_1096,plain,(
    ! [B_197,A_198] :
      ( r1_tarski(k9_relat_1(B_197,A_198),k2_relat_1(B_197))
      | ~ v1_relat_1(B_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1102,plain,(
    ! [A_198] :
      ( r1_tarski(k9_relat_1('#skF_9',A_198),'#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_931,c_1096])).

tff(c_1104,plain,(
    ! [A_198] : r1_tarski(k9_relat_1('#skF_9',A_198),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_1102])).

tff(c_1171,plain,(
    ! [C_210,B_211,A_212] :
      ( r2_hidden(C_210,B_211)
      | ~ r2_hidden(C_210,A_212)
      | ~ r1_tarski(A_212,B_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1292,plain,(
    ! [A_239,B_240] :
      ( r2_hidden('#skF_1'(A_239),B_240)
      | ~ r1_tarski(A_239,B_240)
      | v1_xboole_0(A_239) ) ),
    inference(resolution,[status(thm)],[c_4,c_1171])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1304,plain,(
    ! [B_241,A_242] :
      ( ~ v1_xboole_0(B_241)
      | ~ r1_tarski(A_242,B_241)
      | v1_xboole_0(A_242) ) ),
    inference(resolution,[status(thm)],[c_1292,c_2])).

tff(c_1310,plain,(
    ! [A_198] :
      ( ~ v1_xboole_0('#skF_9')
      | v1_xboole_0(k9_relat_1('#skF_9',A_198)) ) ),
    inference(resolution,[status(thm)],[c_1104,c_1304])).

tff(c_1332,plain,(
    ! [A_243] : v1_xboole_0(k9_relat_1('#skF_9',A_243)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_933,c_1310])).

tff(c_935,plain,(
    ! [A_10] :
      ( A_10 = '#skF_9'
      | ~ v1_xboole_0(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_926,c_12])).

tff(c_1343,plain,(
    ! [A_243] : k9_relat_1('#skF_9',A_243) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1332,c_935])).

tff(c_1279,plain,(
    ! [A_234,B_235,C_236,D_237] :
      ( k7_relset_1(A_234,B_235,C_236,D_237) = k9_relat_1(C_236,D_237)
      | ~ m1_subset_1(C_236,k1_zfmisc_1(k2_zfmisc_1(A_234,B_235))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1282,plain,(
    ! [D_237] : k7_relset_1(k1_tarski('#skF_6'),'#skF_7','#skF_9',D_237) = k9_relat_1('#skF_9',D_237) ),
    inference(resolution,[status(thm)],[c_64,c_1279])).

tff(c_1382,plain,(
    ! [D_237] : k7_relset_1(k1_tarski('#skF_6'),'#skF_7','#skF_9',D_237) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1343,c_1282])).

tff(c_1049,plain,(
    ! [A_191,B_192] :
      ( r2_hidden('#skF_2'(A_191,B_192),A_191)
      | r1_tarski(A_191,B_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1065,plain,(
    ! [A_194,B_195] :
      ( ~ v1_xboole_0(A_194)
      | r1_tarski(A_194,B_195) ) ),
    inference(resolution,[status(thm)],[c_1049,c_2])).

tff(c_1078,plain,(
    ~ v1_xboole_0(k7_relset_1(k1_tarski('#skF_6'),'#skF_7','#skF_9','#skF_8')) ),
    inference(resolution,[status(thm)],[c_1065,c_60])).

tff(c_1383,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1382,c_1078])).

tff(c_1387,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_933,c_1383])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:17:42 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.53/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.56  
% 3.53/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.56  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_2 > #skF_5 > #skF_4
% 3.53/1.56  
% 3.53/1.56  %Foreground sorts:
% 3.53/1.56  
% 3.53/1.56  
% 3.53/1.56  %Background operators:
% 3.53/1.56  
% 3.53/1.56  
% 3.53/1.56  %Foreground operators:
% 3.53/1.56  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.53/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.53/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.53/1.56  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.53/1.56  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.53/1.56  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.53/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.53/1.56  tff('#skF_7', type, '#skF_7': $i).
% 3.53/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.53/1.56  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.53/1.56  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.53/1.56  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.53/1.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.53/1.56  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.53/1.56  tff('#skF_6', type, '#skF_6': $i).
% 3.53/1.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.53/1.56  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.53/1.56  tff('#skF_9', type, '#skF_9': $i).
% 3.53/1.56  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.53/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.53/1.56  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.53/1.56  tff('#skF_8', type, '#skF_8': $i).
% 3.53/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.53/1.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.53/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.53/1.56  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.53/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.53/1.56  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.53/1.56  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.53/1.56  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.53/1.56  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.53/1.56  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.53/1.56  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.53/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.53/1.56  
% 3.53/1.58  tff(f_85, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.53/1.58  tff(f_132, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 3.53/1.58  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.53/1.58  tff(f_89, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 3.53/1.58  tff(f_97, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 3.53/1.58  tff(f_105, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 3.53/1.58  tff(f_120, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.53/1.58  tff(f_116, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.53/1.58  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.53/1.58  tff(f_56, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.53/1.58  tff(f_44, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.53/1.58  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.53/1.58  tff(f_110, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.53/1.58  tff(f_83, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc11_relat_1)).
% 3.53/1.58  tff(f_42, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.53/1.58  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.53/1.58  tff(c_42, plain, (![A_44, B_45]: (v1_relat_1(k2_zfmisc_1(A_44, B_45)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.53/1.58  tff(c_64, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_6'), '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.53/1.58  tff(c_229, plain, (![B_86, A_87]: (v1_relat_1(B_86) | ~m1_subset_1(B_86, k1_zfmisc_1(A_87)) | ~v1_relat_1(A_87))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.53/1.58  tff(c_232, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_6'), '#skF_7'))), inference(resolution, [status(thm)], [c_64, c_229])).
% 3.53/1.58  tff(c_235, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_232])).
% 3.53/1.58  tff(c_44, plain, (![B_47, A_46]: (r1_tarski(k9_relat_1(B_47, A_46), k2_relat_1(B_47)) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.53/1.58  tff(c_48, plain, (![A_48]: (k1_relat_1(A_48)!=k1_xboole_0 | k1_xboole_0=A_48 | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.53/1.58  tff(c_242, plain, (k1_relat_1('#skF_9')!=k1_xboole_0 | k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_235, c_48])).
% 3.53/1.58  tff(c_244, plain, (k1_relat_1('#skF_9')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_242])).
% 3.53/1.58  tff(c_68, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.53/1.58  tff(c_50, plain, (![B_50, A_49]: (k1_tarski(k1_funct_1(B_50, A_49))=k2_relat_1(B_50) | k1_tarski(A_49)!=k1_relat_1(B_50) | ~v1_funct_1(B_50) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.53/1.58  tff(c_484, plain, (![A_132, B_133, C_134, D_135]: (k7_relset_1(A_132, B_133, C_134, D_135)=k9_relat_1(C_134, D_135) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(A_132, B_133))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.53/1.58  tff(c_487, plain, (![D_135]: (k7_relset_1(k1_tarski('#skF_6'), '#skF_7', '#skF_9', D_135)=k9_relat_1('#skF_9', D_135))), inference(resolution, [status(thm)], [c_64, c_484])).
% 3.53/1.58  tff(c_60, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_6'), '#skF_7', '#skF_9', '#skF_8'), k1_tarski(k1_funct_1('#skF_9', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.53/1.58  tff(c_522, plain, (~r1_tarski(k9_relat_1('#skF_9', '#skF_8'), k1_tarski(k1_funct_1('#skF_9', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_487, c_60])).
% 3.53/1.58  tff(c_546, plain, (~r1_tarski(k9_relat_1('#skF_9', '#skF_8'), k2_relat_1('#skF_9')) | k1_tarski('#skF_6')!=k1_relat_1('#skF_9') | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_50, c_522])).
% 3.53/1.58  tff(c_551, plain, (~r1_tarski(k9_relat_1('#skF_9', '#skF_8'), k2_relat_1('#skF_9')) | k1_tarski('#skF_6')!=k1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_235, c_68, c_546])).
% 3.53/1.58  tff(c_555, plain, (k1_tarski('#skF_6')!=k1_relat_1('#skF_9')), inference(splitLeft, [status(thm)], [c_551])).
% 3.53/1.58  tff(c_318, plain, (![C_102, A_103, B_104]: (v4_relat_1(C_102, A_103) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.53/1.58  tff(c_322, plain, (v4_relat_1('#skF_9', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_64, c_318])).
% 3.53/1.58  tff(c_349, plain, (![B_113, A_114]: (r1_tarski(k1_relat_1(B_113), A_114) | ~v4_relat_1(B_113, A_114) | ~v1_relat_1(B_113))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.53/1.58  tff(c_22, plain, (![B_19, A_18]: (k1_tarski(B_19)=A_18 | k1_xboole_0=A_18 | ~r1_tarski(A_18, k1_tarski(B_19)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.53/1.58  tff(c_871, plain, (![B_182, B_183]: (k1_tarski(B_182)=k1_relat_1(B_183) | k1_relat_1(B_183)=k1_xboole_0 | ~v4_relat_1(B_183, k1_tarski(B_182)) | ~v1_relat_1(B_183))), inference(resolution, [status(thm)], [c_349, c_22])).
% 3.53/1.58  tff(c_877, plain, (k1_tarski('#skF_6')=k1_relat_1('#skF_9') | k1_relat_1('#skF_9')=k1_xboole_0 | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_322, c_871])).
% 3.53/1.58  tff(c_880, plain, (k1_tarski('#skF_6')=k1_relat_1('#skF_9') | k1_relat_1('#skF_9')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_235, c_877])).
% 3.53/1.58  tff(c_882, plain, $false, inference(negUnitSimplification, [status(thm)], [c_244, c_555, c_880])).
% 3.53/1.58  tff(c_883, plain, (~r1_tarski(k9_relat_1('#skF_9', '#skF_8'), k2_relat_1('#skF_9'))), inference(splitRight, [status(thm)], [c_551])).
% 3.53/1.58  tff(c_918, plain, (~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_44, c_883])).
% 3.53/1.58  tff(c_925, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_235, c_918])).
% 3.53/1.58  tff(c_926, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_242])).
% 3.53/1.58  tff(c_14, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.53/1.58  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.53/1.58  tff(c_110, plain, (![B_74, A_75]: (~r1_tarski(B_74, A_75) | ~r2_hidden(A_75, B_74))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.53/1.58  tff(c_119, plain, (![A_76]: (~r1_tarski(A_76, '#skF_1'(A_76)) | v1_xboole_0(A_76))), inference(resolution, [status(thm)], [c_4, c_110])).
% 3.53/1.58  tff(c_124, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_119])).
% 3.53/1.58  tff(c_933, plain, (v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_926, c_124])).
% 3.53/1.58  tff(c_73, plain, (![A_64]: (v1_xboole_0(k2_relat_1(A_64)) | ~v1_xboole_0(A_64))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.53/1.58  tff(c_12, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.53/1.58  tff(c_77, plain, (![A_64]: (k2_relat_1(A_64)=k1_xboole_0 | ~v1_xboole_0(A_64))), inference(resolution, [status(thm)], [c_73, c_12])).
% 3.53/1.58  tff(c_135, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_124, c_77])).
% 3.53/1.58  tff(c_931, plain, (k2_relat_1('#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_926, c_926, c_135])).
% 3.53/1.58  tff(c_1096, plain, (![B_197, A_198]: (r1_tarski(k9_relat_1(B_197, A_198), k2_relat_1(B_197)) | ~v1_relat_1(B_197))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.53/1.58  tff(c_1102, plain, (![A_198]: (r1_tarski(k9_relat_1('#skF_9', A_198), '#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_931, c_1096])).
% 3.53/1.58  tff(c_1104, plain, (![A_198]: (r1_tarski(k9_relat_1('#skF_9', A_198), '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_235, c_1102])).
% 3.53/1.58  tff(c_1171, plain, (![C_210, B_211, A_212]: (r2_hidden(C_210, B_211) | ~r2_hidden(C_210, A_212) | ~r1_tarski(A_212, B_211))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.53/1.58  tff(c_1292, plain, (![A_239, B_240]: (r2_hidden('#skF_1'(A_239), B_240) | ~r1_tarski(A_239, B_240) | v1_xboole_0(A_239))), inference(resolution, [status(thm)], [c_4, c_1171])).
% 3.53/1.58  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.53/1.58  tff(c_1304, plain, (![B_241, A_242]: (~v1_xboole_0(B_241) | ~r1_tarski(A_242, B_241) | v1_xboole_0(A_242))), inference(resolution, [status(thm)], [c_1292, c_2])).
% 3.53/1.58  tff(c_1310, plain, (![A_198]: (~v1_xboole_0('#skF_9') | v1_xboole_0(k9_relat_1('#skF_9', A_198)))), inference(resolution, [status(thm)], [c_1104, c_1304])).
% 3.53/1.58  tff(c_1332, plain, (![A_243]: (v1_xboole_0(k9_relat_1('#skF_9', A_243)))), inference(demodulation, [status(thm), theory('equality')], [c_933, c_1310])).
% 3.53/1.58  tff(c_935, plain, (![A_10]: (A_10='#skF_9' | ~v1_xboole_0(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_926, c_12])).
% 3.53/1.58  tff(c_1343, plain, (![A_243]: (k9_relat_1('#skF_9', A_243)='#skF_9')), inference(resolution, [status(thm)], [c_1332, c_935])).
% 3.53/1.58  tff(c_1279, plain, (![A_234, B_235, C_236, D_237]: (k7_relset_1(A_234, B_235, C_236, D_237)=k9_relat_1(C_236, D_237) | ~m1_subset_1(C_236, k1_zfmisc_1(k2_zfmisc_1(A_234, B_235))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.53/1.58  tff(c_1282, plain, (![D_237]: (k7_relset_1(k1_tarski('#skF_6'), '#skF_7', '#skF_9', D_237)=k9_relat_1('#skF_9', D_237))), inference(resolution, [status(thm)], [c_64, c_1279])).
% 3.53/1.58  tff(c_1382, plain, (![D_237]: (k7_relset_1(k1_tarski('#skF_6'), '#skF_7', '#skF_9', D_237)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1343, c_1282])).
% 3.53/1.58  tff(c_1049, plain, (![A_191, B_192]: (r2_hidden('#skF_2'(A_191, B_192), A_191) | r1_tarski(A_191, B_192))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.53/1.58  tff(c_1065, plain, (![A_194, B_195]: (~v1_xboole_0(A_194) | r1_tarski(A_194, B_195))), inference(resolution, [status(thm)], [c_1049, c_2])).
% 3.53/1.58  tff(c_1078, plain, (~v1_xboole_0(k7_relset_1(k1_tarski('#skF_6'), '#skF_7', '#skF_9', '#skF_8'))), inference(resolution, [status(thm)], [c_1065, c_60])).
% 3.53/1.58  tff(c_1383, plain, (~v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1382, c_1078])).
% 3.53/1.58  tff(c_1387, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_933, c_1383])).
% 3.53/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.58  
% 3.53/1.58  Inference rules
% 3.53/1.58  ----------------------
% 3.53/1.58  #Ref     : 1
% 3.53/1.58  #Sup     : 272
% 3.53/1.58  #Fact    : 0
% 3.53/1.58  #Define  : 0
% 3.53/1.58  #Split   : 3
% 3.53/1.58  #Chain   : 0
% 3.53/1.58  #Close   : 0
% 3.53/1.58  
% 3.53/1.58  Ordering : KBO
% 3.53/1.58  
% 3.53/1.58  Simplification rules
% 3.53/1.58  ----------------------
% 3.53/1.58  #Subsume      : 27
% 3.53/1.58  #Demod        : 162
% 3.53/1.58  #Tautology    : 127
% 3.53/1.58  #SimpNegUnit  : 1
% 3.53/1.58  #BackRed      : 24
% 3.53/1.58  
% 3.53/1.58  #Partial instantiations: 0
% 3.53/1.58  #Strategies tried      : 1
% 3.53/1.58  
% 3.53/1.58  Timing (in seconds)
% 3.53/1.58  ----------------------
% 3.53/1.58  Preprocessing        : 0.33
% 3.53/1.58  Parsing              : 0.17
% 3.53/1.58  CNF conversion       : 0.02
% 3.53/1.58  Main loop            : 0.44
% 3.53/1.58  Inferencing          : 0.16
% 3.53/1.58  Reduction            : 0.14
% 3.53/1.58  Demodulation         : 0.09
% 3.53/1.58  BG Simplification    : 0.02
% 3.53/1.58  Subsumption          : 0.08
% 3.53/1.58  Abstraction          : 0.02
% 3.53/1.58  MUC search           : 0.00
% 3.53/1.58  Cooper               : 0.00
% 3.53/1.58  Total                : 0.81
% 3.53/1.58  Index Insertion      : 0.00
% 3.53/1.58  Index Deletion       : 0.00
% 3.53/1.58  Index Matching       : 0.00
% 3.53/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
