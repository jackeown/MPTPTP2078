%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:13 EST 2020

% Result     : Theorem 5.30s
% Output     : CNFRefutation 5.60s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 137 expanded)
%              Number of leaves         :   44 (  68 expanded)
%              Depth                    :    9
%              Number of atoms          :  146 ( 268 expanded)
%              Number of equality atoms :   38 (  69 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_1 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_147,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

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

tff(f_117,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_135,axiom,(
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

tff(f_48,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_50,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v5_relat_1(C,A)
        & v1_funct_1(C) )
     => ( r2_hidden(B,k1_relat_1(C))
       => m1_subset_1(k1_funct_1(C,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_113,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_86,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

tff(c_80,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_7'),'#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_1271,plain,(
    ! [C_207,A_208,B_209] :
      ( v1_relat_1(C_207)
      | ~ m1_subset_1(C_207,k1_zfmisc_1(k2_zfmisc_1(A_208,B_209))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1275,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_80,c_1271])).

tff(c_84,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_199,plain,(
    ! [C_104,B_105,A_106] :
      ( v5_relat_1(C_104,B_105)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_106,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_203,plain,(
    v5_relat_1('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_80,c_199])).

tff(c_180,plain,(
    ! [C_95,A_96,B_97] :
      ( v1_relat_1(C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_184,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_80,c_180])).

tff(c_78,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_82,plain,(
    v1_funct_2('#skF_9',k1_tarski('#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_393,plain,(
    ! [A_133,B_134,C_135] :
      ( k1_relset_1(A_133,B_134,C_135) = k1_relat_1(C_135)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_397,plain,(
    k1_relset_1(k1_tarski('#skF_7'),'#skF_8','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_80,c_393])).

tff(c_984,plain,(
    ! [B_194,A_195,C_196] :
      ( k1_xboole_0 = B_194
      | k1_relset_1(A_195,B_194,C_196) = A_195
      | ~ v1_funct_2(C_196,A_195,B_194)
      | ~ m1_subset_1(C_196,k1_zfmisc_1(k2_zfmisc_1(A_195,B_194))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_987,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relset_1(k1_tarski('#skF_7'),'#skF_8','#skF_9') = k1_tarski('#skF_7')
    | ~ v1_funct_2('#skF_9',k1_tarski('#skF_7'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_80,c_984])).

tff(c_990,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_tarski('#skF_7') = k1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_397,c_987])).

tff(c_991,plain,(
    k1_tarski('#skF_7') = k1_relat_1('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_990])).

tff(c_30,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_123,plain,(
    ! [A_83,B_84] : k1_enumset1(A_83,A_83,B_84) = k2_tarski(A_83,B_84) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_12,plain,(
    ! [E_11,B_6,C_7] : r2_hidden(E_11,k1_enumset1(E_11,B_6,C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_147,plain,(
    ! [A_88,B_89] : r2_hidden(A_88,k2_tarski(A_88,B_89)) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_12])).

tff(c_153,plain,(
    ! [A_12] : r2_hidden(A_12,k1_tarski(A_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_147])).

tff(c_1011,plain,(
    r2_hidden('#skF_7',k1_relat_1('#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_991,c_153])).

tff(c_52,plain,(
    ! [C_45,B_44,A_43] :
      ( m1_subset_1(k1_funct_1(C_45,B_44),A_43)
      | ~ r2_hidden(B_44,k1_relat_1(C_45))
      | ~ v1_funct_1(C_45)
      | ~ v5_relat_1(C_45,A_43)
      | ~ v1_relat_1(C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1025,plain,(
    ! [A_43] :
      ( m1_subset_1(k1_funct_1('#skF_9','#skF_7'),A_43)
      | ~ v1_funct_1('#skF_9')
      | ~ v5_relat_1('#skF_9',A_43)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1011,c_52])).

tff(c_1187,plain,(
    ! [A_206] :
      ( m1_subset_1(k1_funct_1('#skF_9','#skF_7'),A_206)
      | ~ v5_relat_1('#skF_9',A_206) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_84,c_1025])).

tff(c_155,plain,(
    ! [A_90,B_91] :
      ( r2_hidden(A_90,B_91)
      | v1_xboole_0(B_91)
      | ~ m1_subset_1(A_90,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_76,plain,(
    ~ r2_hidden(k1_funct_1('#skF_9','#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_163,plain,
    ( v1_xboole_0('#skF_8')
    | ~ m1_subset_1(k1_funct_1('#skF_9','#skF_7'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_155,c_76])).

tff(c_179,plain,(
    ~ m1_subset_1(k1_funct_1('#skF_9','#skF_7'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_163])).

tff(c_1246,plain,(
    ~ v5_relat_1('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_1187,c_179])).

tff(c_1264,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_1246])).

tff(c_1265,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_163])).

tff(c_1295,plain,(
    ! [C_219,B_220,A_221] :
      ( v1_xboole_0(C_219)
      | ~ m1_subset_1(C_219,k1_zfmisc_1(k2_zfmisc_1(B_220,A_221)))
      | ~ v1_xboole_0(A_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1298,plain,
    ( v1_xboole_0('#skF_9')
    | ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_80,c_1295])).

tff(c_1301,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1265,c_1298])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1665,plain,(
    ! [B_286,A_287] :
      ( r2_hidden(k4_tarski(B_286,k1_funct_1(A_287,B_286)),A_287)
      | ~ r2_hidden(B_286,k1_relat_1(A_287))
      | ~ v1_funct_1(A_287)
      | ~ v1_relat_1(A_287) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1685,plain,(
    ! [A_288,B_289] :
      ( ~ v1_xboole_0(A_288)
      | ~ r2_hidden(B_289,k1_relat_1(A_288))
      | ~ v1_funct_1(A_288)
      | ~ v1_relat_1(A_288) ) ),
    inference(resolution,[status(thm)],[c_1665,c_2])).

tff(c_1708,plain,(
    ! [A_288] :
      ( ~ v1_xboole_0(A_288)
      | ~ v1_funct_1(A_288)
      | ~ v1_relat_1(A_288)
      | v1_xboole_0(k1_relat_1(A_288)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1685])).

tff(c_1444,plain,(
    ! [A_236,B_237,C_238] :
      ( k1_relset_1(A_236,B_237,C_238) = k1_relat_1(C_238)
      | ~ m1_subset_1(C_238,k1_zfmisc_1(k2_zfmisc_1(A_236,B_237))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1448,plain,(
    k1_relset_1(k1_tarski('#skF_7'),'#skF_8','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_80,c_1444])).

tff(c_1826,plain,(
    ! [B_301,A_302,C_303] :
      ( k1_xboole_0 = B_301
      | k1_relset_1(A_302,B_301,C_303) = A_302
      | ~ v1_funct_2(C_303,A_302,B_301)
      | ~ m1_subset_1(C_303,k1_zfmisc_1(k2_zfmisc_1(A_302,B_301))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1829,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relset_1(k1_tarski('#skF_7'),'#skF_8','#skF_9') = k1_tarski('#skF_7')
    | ~ v1_funct_2('#skF_9',k1_tarski('#skF_7'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_80,c_1826])).

tff(c_1832,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_tarski('#skF_7') = k1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1448,c_1829])).

tff(c_1833,plain,(
    k1_tarski('#skF_7') = k1_relat_1('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1832])).

tff(c_101,plain,(
    ! [E_67,A_68,B_69] : r2_hidden(E_67,k1_enumset1(A_68,B_69,E_67)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_105,plain,(
    ! [A_68,B_69,E_67] : ~ v1_xboole_0(k1_enumset1(A_68,B_69,E_67)) ),
    inference(resolution,[status(thm)],[c_101,c_2])).

tff(c_143,plain,(
    ! [A_85,B_86] : ~ v1_xboole_0(k2_tarski(A_85,B_86)) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_105])).

tff(c_145,plain,(
    ! [A_12] : ~ v1_xboole_0(k1_tarski(A_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_143])).

tff(c_1855,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1833,c_145])).

tff(c_1862,plain,
    ( ~ v1_xboole_0('#skF_9')
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_1708,c_1855])).

tff(c_1866,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1275,c_84,c_1301,c_1862])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:56:21 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.30/2.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.60/2.31  
% 5.60/2.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.60/2.31  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_1 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_5
% 5.60/2.31  
% 5.60/2.31  %Foreground sorts:
% 5.60/2.31  
% 5.60/2.31  
% 5.60/2.31  %Background operators:
% 5.60/2.31  
% 5.60/2.31  
% 5.60/2.31  %Foreground operators:
% 5.60/2.31  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 5.60/2.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.60/2.31  tff('#skF_4', type, '#skF_4': $i > $i).
% 5.60/2.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.60/2.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.60/2.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.60/2.31  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.60/2.31  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.60/2.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.60/2.31  tff('#skF_7', type, '#skF_7': $i).
% 5.60/2.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.60/2.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.60/2.31  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.60/2.31  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 5.60/2.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.60/2.31  tff('#skF_9', type, '#skF_9': $i).
% 5.60/2.31  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.60/2.31  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.60/2.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.60/2.31  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.60/2.31  tff('#skF_8', type, '#skF_8': $i).
% 5.60/2.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.60/2.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.60/2.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.60/2.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.60/2.31  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.60/2.31  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 5.60/2.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.60/2.31  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 5.60/2.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.60/2.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.60/2.31  
% 5.60/2.33  tff(f_147, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_2)).
% 5.60/2.33  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.60/2.33  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.60/2.33  tff(f_117, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.60/2.33  tff(f_135, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.60/2.33  tff(f_48, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 5.60/2.33  tff(f_50, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 5.60/2.33  tff(f_46, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 5.60/2.33  tff(f_96, axiom, (![A, B, C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (r2_hidden(B, k1_relat_1(C)) => m1_subset_1(k1_funct_1(C, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t176_funct_1)).
% 5.60/2.33  tff(f_58, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 5.60/2.33  tff(f_113, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 5.60/2.33  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.60/2.33  tff(f_86, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_funct_1)).
% 5.60/2.33  tff(c_80, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_7'), '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_147])).
% 5.60/2.33  tff(c_1271, plain, (![C_207, A_208, B_209]: (v1_relat_1(C_207) | ~m1_subset_1(C_207, k1_zfmisc_1(k2_zfmisc_1(A_208, B_209))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.60/2.33  tff(c_1275, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_80, c_1271])).
% 5.60/2.33  tff(c_84, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_147])).
% 5.60/2.33  tff(c_199, plain, (![C_104, B_105, A_106]: (v5_relat_1(C_104, B_105) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_106, B_105))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.60/2.33  tff(c_203, plain, (v5_relat_1('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_80, c_199])).
% 5.60/2.33  tff(c_180, plain, (![C_95, A_96, B_97]: (v1_relat_1(C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.60/2.33  tff(c_184, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_80, c_180])).
% 5.60/2.33  tff(c_78, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_147])).
% 5.60/2.33  tff(c_82, plain, (v1_funct_2('#skF_9', k1_tarski('#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_147])).
% 5.60/2.33  tff(c_393, plain, (![A_133, B_134, C_135]: (k1_relset_1(A_133, B_134, C_135)=k1_relat_1(C_135) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.60/2.33  tff(c_397, plain, (k1_relset_1(k1_tarski('#skF_7'), '#skF_8', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_80, c_393])).
% 5.60/2.33  tff(c_984, plain, (![B_194, A_195, C_196]: (k1_xboole_0=B_194 | k1_relset_1(A_195, B_194, C_196)=A_195 | ~v1_funct_2(C_196, A_195, B_194) | ~m1_subset_1(C_196, k1_zfmisc_1(k2_zfmisc_1(A_195, B_194))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.60/2.33  tff(c_987, plain, (k1_xboole_0='#skF_8' | k1_relset_1(k1_tarski('#skF_7'), '#skF_8', '#skF_9')=k1_tarski('#skF_7') | ~v1_funct_2('#skF_9', k1_tarski('#skF_7'), '#skF_8')), inference(resolution, [status(thm)], [c_80, c_984])).
% 5.60/2.33  tff(c_990, plain, (k1_xboole_0='#skF_8' | k1_tarski('#skF_7')=k1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_397, c_987])).
% 5.60/2.33  tff(c_991, plain, (k1_tarski('#skF_7')=k1_relat_1('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_78, c_990])).
% 5.60/2.33  tff(c_30, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.60/2.33  tff(c_123, plain, (![A_83, B_84]: (k1_enumset1(A_83, A_83, B_84)=k2_tarski(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.60/2.33  tff(c_12, plain, (![E_11, B_6, C_7]: (r2_hidden(E_11, k1_enumset1(E_11, B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.60/2.33  tff(c_147, plain, (![A_88, B_89]: (r2_hidden(A_88, k2_tarski(A_88, B_89)))), inference(superposition, [status(thm), theory('equality')], [c_123, c_12])).
% 5.60/2.33  tff(c_153, plain, (![A_12]: (r2_hidden(A_12, k1_tarski(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_147])).
% 5.60/2.33  tff(c_1011, plain, (r2_hidden('#skF_7', k1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_991, c_153])).
% 5.60/2.33  tff(c_52, plain, (![C_45, B_44, A_43]: (m1_subset_1(k1_funct_1(C_45, B_44), A_43) | ~r2_hidden(B_44, k1_relat_1(C_45)) | ~v1_funct_1(C_45) | ~v5_relat_1(C_45, A_43) | ~v1_relat_1(C_45))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.60/2.33  tff(c_1025, plain, (![A_43]: (m1_subset_1(k1_funct_1('#skF_9', '#skF_7'), A_43) | ~v1_funct_1('#skF_9') | ~v5_relat_1('#skF_9', A_43) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_1011, c_52])).
% 5.60/2.33  tff(c_1187, plain, (![A_206]: (m1_subset_1(k1_funct_1('#skF_9', '#skF_7'), A_206) | ~v5_relat_1('#skF_9', A_206))), inference(demodulation, [status(thm), theory('equality')], [c_184, c_84, c_1025])).
% 5.60/2.33  tff(c_155, plain, (![A_90, B_91]: (r2_hidden(A_90, B_91) | v1_xboole_0(B_91) | ~m1_subset_1(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.60/2.33  tff(c_76, plain, (~r2_hidden(k1_funct_1('#skF_9', '#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_147])).
% 5.60/2.33  tff(c_163, plain, (v1_xboole_0('#skF_8') | ~m1_subset_1(k1_funct_1('#skF_9', '#skF_7'), '#skF_8')), inference(resolution, [status(thm)], [c_155, c_76])).
% 5.60/2.33  tff(c_179, plain, (~m1_subset_1(k1_funct_1('#skF_9', '#skF_7'), '#skF_8')), inference(splitLeft, [status(thm)], [c_163])).
% 5.60/2.33  tff(c_1246, plain, (~v5_relat_1('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_1187, c_179])).
% 5.60/2.33  tff(c_1264, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_203, c_1246])).
% 5.60/2.33  tff(c_1265, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_163])).
% 5.60/2.33  tff(c_1295, plain, (![C_219, B_220, A_221]: (v1_xboole_0(C_219) | ~m1_subset_1(C_219, k1_zfmisc_1(k2_zfmisc_1(B_220, A_221))) | ~v1_xboole_0(A_221))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.60/2.33  tff(c_1298, plain, (v1_xboole_0('#skF_9') | ~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_80, c_1295])).
% 5.60/2.33  tff(c_1301, plain, (v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1265, c_1298])).
% 5.60/2.33  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.60/2.33  tff(c_1665, plain, (![B_286, A_287]: (r2_hidden(k4_tarski(B_286, k1_funct_1(A_287, B_286)), A_287) | ~r2_hidden(B_286, k1_relat_1(A_287)) | ~v1_funct_1(A_287) | ~v1_relat_1(A_287))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.60/2.33  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.60/2.33  tff(c_1685, plain, (![A_288, B_289]: (~v1_xboole_0(A_288) | ~r2_hidden(B_289, k1_relat_1(A_288)) | ~v1_funct_1(A_288) | ~v1_relat_1(A_288))), inference(resolution, [status(thm)], [c_1665, c_2])).
% 5.60/2.33  tff(c_1708, plain, (![A_288]: (~v1_xboole_0(A_288) | ~v1_funct_1(A_288) | ~v1_relat_1(A_288) | v1_xboole_0(k1_relat_1(A_288)))), inference(resolution, [status(thm)], [c_4, c_1685])).
% 5.60/2.33  tff(c_1444, plain, (![A_236, B_237, C_238]: (k1_relset_1(A_236, B_237, C_238)=k1_relat_1(C_238) | ~m1_subset_1(C_238, k1_zfmisc_1(k2_zfmisc_1(A_236, B_237))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.60/2.33  tff(c_1448, plain, (k1_relset_1(k1_tarski('#skF_7'), '#skF_8', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_80, c_1444])).
% 5.60/2.33  tff(c_1826, plain, (![B_301, A_302, C_303]: (k1_xboole_0=B_301 | k1_relset_1(A_302, B_301, C_303)=A_302 | ~v1_funct_2(C_303, A_302, B_301) | ~m1_subset_1(C_303, k1_zfmisc_1(k2_zfmisc_1(A_302, B_301))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.60/2.33  tff(c_1829, plain, (k1_xboole_0='#skF_8' | k1_relset_1(k1_tarski('#skF_7'), '#skF_8', '#skF_9')=k1_tarski('#skF_7') | ~v1_funct_2('#skF_9', k1_tarski('#skF_7'), '#skF_8')), inference(resolution, [status(thm)], [c_80, c_1826])).
% 5.60/2.33  tff(c_1832, plain, (k1_xboole_0='#skF_8' | k1_tarski('#skF_7')=k1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_1448, c_1829])).
% 5.60/2.33  tff(c_1833, plain, (k1_tarski('#skF_7')=k1_relat_1('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_78, c_1832])).
% 5.60/2.33  tff(c_101, plain, (![E_67, A_68, B_69]: (r2_hidden(E_67, k1_enumset1(A_68, B_69, E_67)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.60/2.33  tff(c_105, plain, (![A_68, B_69, E_67]: (~v1_xboole_0(k1_enumset1(A_68, B_69, E_67)))), inference(resolution, [status(thm)], [c_101, c_2])).
% 5.60/2.33  tff(c_143, plain, (![A_85, B_86]: (~v1_xboole_0(k2_tarski(A_85, B_86)))), inference(superposition, [status(thm), theory('equality')], [c_123, c_105])).
% 5.60/2.33  tff(c_145, plain, (![A_12]: (~v1_xboole_0(k1_tarski(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_143])).
% 5.60/2.33  tff(c_1855, plain, (~v1_xboole_0(k1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_1833, c_145])).
% 5.60/2.33  tff(c_1862, plain, (~v1_xboole_0('#skF_9') | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_1708, c_1855])).
% 5.60/2.33  tff(c_1866, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1275, c_84, c_1301, c_1862])).
% 5.60/2.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.60/2.33  
% 5.60/2.33  Inference rules
% 5.60/2.33  ----------------------
% 5.60/2.34  #Ref     : 2
% 5.60/2.34  #Sup     : 407
% 5.60/2.34  #Fact    : 6
% 5.60/2.34  #Define  : 0
% 5.60/2.34  #Split   : 4
% 5.60/2.34  #Chain   : 0
% 5.60/2.34  #Close   : 0
% 5.60/2.34  
% 5.60/2.34  Ordering : KBO
% 5.60/2.34  
% 5.60/2.34  Simplification rules
% 5.60/2.34  ----------------------
% 5.60/2.34  #Subsume      : 96
% 5.60/2.34  #Demod        : 89
% 5.60/2.34  #Tautology    : 110
% 5.60/2.34  #SimpNegUnit  : 25
% 5.60/2.34  #BackRed      : 10
% 5.60/2.34  
% 5.60/2.34  #Partial instantiations: 0
% 5.60/2.34  #Strategies tried      : 1
% 5.60/2.34  
% 5.60/2.34  Timing (in seconds)
% 5.60/2.34  ----------------------
% 5.60/2.34  Preprocessing        : 0.58
% 5.60/2.34  Parsing              : 0.29
% 5.60/2.34  CNF conversion       : 0.05
% 5.60/2.34  Main loop            : 0.94
% 5.60/2.34  Inferencing          : 0.35
% 5.60/2.34  Reduction            : 0.27
% 5.60/2.34  Demodulation         : 0.19
% 5.60/2.34  BG Simplification    : 0.05
% 5.60/2.34  Subsumption          : 0.18
% 5.60/2.34  Abstraction          : 0.05
% 5.60/2.34  MUC search           : 0.00
% 5.60/2.34  Cooper               : 0.00
% 5.60/2.34  Total                : 1.58
% 5.60/2.34  Index Insertion      : 0.00
% 5.60/2.34  Index Deletion       : 0.00
% 5.60/2.34  Index Matching       : 0.00
% 5.60/2.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
