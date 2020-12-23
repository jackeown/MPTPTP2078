%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:28 EST 2020

% Result     : Theorem 4.47s
% Output     : CNFRefutation 4.47s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 223 expanded)
%              Number of leaves         :   46 (  93 expanded)
%              Depth                    :   11
%              Number of atoms          :  171 ( 452 expanded)
%              Number of equality atoms :   82 ( 198 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_152,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_42,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_63,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_140,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_122,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
      <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_78,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_135,plain,(
    ! [C_73,A_74,B_75] :
      ( v1_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_143,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_78,c_135])).

tff(c_82,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_42,plain,(
    ! [A_24] :
      ( k1_relat_1(A_24) != k1_xboole_0
      | k1_xboole_0 = A_24
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_152,plain,
    ( k1_relat_1('#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_143,c_42])).

tff(c_164,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_152])).

tff(c_415,plain,(
    ! [B_129,A_130] :
      ( k1_tarski(k1_funct_1(B_129,A_130)) = k2_relat_1(B_129)
      | k1_tarski(A_130) != k1_relat_1(B_129)
      | ~ v1_funct_1(B_129)
      | ~ v1_relat_1(B_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_308,plain,(
    ! [A_109,B_110,C_111] :
      ( k2_relset_1(A_109,B_110,C_111) = k2_relat_1(C_111)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_316,plain,(
    k2_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_78,c_308])).

tff(c_74,plain,(
    k2_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') != k1_tarski(k1_funct_1('#skF_6','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_325,plain,(
    k1_tarski(k1_funct_1('#skF_6','#skF_4')) != k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_74])).

tff(c_424,plain,
    ( k1_tarski('#skF_4') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_415,c_325])).

tff(c_440,plain,(
    k1_tarski('#skF_4') != k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_82,c_424])).

tff(c_251,plain,(
    ! [C_97,A_98,B_99] :
      ( v4_relat_1(C_97,A_98)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_259,plain,(
    v4_relat_1('#skF_6',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_78,c_251])).

tff(c_38,plain,(
    ! [B_23,A_22] :
      ( r1_tarski(k1_relat_1(B_23),A_22)
      | ~ v4_relat_1(B_23,A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_16,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_825,plain,(
    ! [B_186,C_187,A_188] :
      ( k2_tarski(B_186,C_187) = A_188
      | k1_tarski(C_187) = A_188
      | k1_tarski(B_186) = A_188
      | k1_xboole_0 = A_188
      | ~ r1_tarski(A_188,k2_tarski(B_186,C_187)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_842,plain,(
    ! [A_9,A_188] :
      ( k2_tarski(A_9,A_9) = A_188
      | k1_tarski(A_9) = A_188
      | k1_tarski(A_9) = A_188
      | k1_xboole_0 = A_188
      | ~ r1_tarski(A_188,k1_tarski(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_825])).

tff(c_1043,plain,(
    ! [A_231,A_232] :
      ( k1_tarski(A_231) = A_232
      | k1_tarski(A_231) = A_232
      | k1_tarski(A_231) = A_232
      | k1_xboole_0 = A_232
      | ~ r1_tarski(A_232,k1_tarski(A_231)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_842])).

tff(c_1069,plain,(
    ! [A_233,B_234] :
      ( k1_tarski(A_233) = k1_relat_1(B_234)
      | k1_relat_1(B_234) = k1_xboole_0
      | ~ v4_relat_1(B_234,k1_tarski(A_233))
      | ~ v1_relat_1(B_234) ) ),
    inference(resolution,[status(thm)],[c_38,c_1043])).

tff(c_1075,plain,
    ( k1_tarski('#skF_4') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_259,c_1069])).

tff(c_1082,plain,
    ( k1_tarski('#skF_4') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_1075])).

tff(c_1084,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_164,c_440,c_1082])).

tff(c_1085,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_152])).

tff(c_1086,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_152])).

tff(c_1100,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1085,c_1086])).

tff(c_1411,plain,(
    ! [B_297,A_298] :
      ( k1_tarski(k1_funct_1(B_297,A_298)) = k2_relat_1(B_297)
      | k1_tarski(A_298) != k1_relat_1(B_297)
      | ~ v1_funct_1(B_297)
      | ~ v1_relat_1(B_297) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_32,plain,(
    ! [A_18] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1092,plain,(
    ! [A_18] : m1_subset_1('#skF_6',k1_zfmisc_1(A_18)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1085,c_32])).

tff(c_1295,plain,(
    ! [A_280,B_281,C_282] :
      ( k2_relset_1(A_280,B_281,C_282) = k2_relat_1(C_282)
      | ~ m1_subset_1(C_282,k1_zfmisc_1(k2_zfmisc_1(A_280,B_281))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1300,plain,(
    ! [A_280,B_281] : k2_relset_1(A_280,B_281,'#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1092,c_1295])).

tff(c_1316,plain,(
    k1_tarski(k1_funct_1('#skF_6','#skF_4')) != k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1300,c_74])).

tff(c_1417,plain,
    ( k1_tarski('#skF_4') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1411,c_1316])).

tff(c_1436,plain,(
    k1_tarski('#skF_4') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_82,c_1100,c_1417])).

tff(c_76,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_1094,plain,(
    '#skF_5' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1085,c_76])).

tff(c_80,plain,(
    v1_funct_2('#skF_6',k1_tarski('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_72,plain,(
    ! [B_52,A_51,C_53] :
      ( k1_xboole_0 = B_52
      | k1_relset_1(A_51,B_52,C_53) = A_51
      | ~ v1_funct_2(C_53,A_51,B_52)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_1591,plain,(
    ! [B_330,A_331,C_332] :
      ( B_330 = '#skF_6'
      | k1_relset_1(A_331,B_330,C_332) = A_331
      | ~ v1_funct_2(C_332,A_331,B_330)
      | ~ m1_subset_1(C_332,k1_zfmisc_1(k2_zfmisc_1(A_331,B_330))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1085,c_72])).

tff(c_1597,plain,(
    ! [B_333,A_334] :
      ( B_333 = '#skF_6'
      | k1_relset_1(A_334,B_333,'#skF_6') = A_334
      | ~ v1_funct_2('#skF_6',A_334,B_333) ) ),
    inference(resolution,[status(thm)],[c_1092,c_1591])).

tff(c_1606,plain,
    ( '#skF_5' = '#skF_6'
    | k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_tarski('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_1597])).

tff(c_1612,plain,(
    k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_1094,c_1606])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1093,plain,(
    ! [A_8] : r1_tarski('#skF_6',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1085,c_14])).

tff(c_1915,plain,(
    ! [D_391,A_392,B_393,C_394] :
      ( r2_hidden(k4_tarski(D_391,'#skF_3'(A_392,B_393,C_394,D_391)),C_394)
      | ~ r2_hidden(D_391,B_393)
      | k1_relset_1(B_393,A_392,C_394) != B_393
      | ~ m1_subset_1(C_394,k1_zfmisc_1(k2_zfmisc_1(B_393,A_392))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_46,plain,(
    ! [B_28,A_27] :
      ( ~ r1_tarski(B_28,A_27)
      | ~ r2_hidden(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2195,plain,(
    ! [C_432,D_433,A_434,B_435] :
      ( ~ r1_tarski(C_432,k4_tarski(D_433,'#skF_3'(A_434,B_435,C_432,D_433)))
      | ~ r2_hidden(D_433,B_435)
      | k1_relset_1(B_435,A_434,C_432) != B_435
      | ~ m1_subset_1(C_432,k1_zfmisc_1(k2_zfmisc_1(B_435,A_434))) ) ),
    inference(resolution,[status(thm)],[c_1915,c_46])).

tff(c_2207,plain,(
    ! [D_433,B_435,A_434] :
      ( ~ r2_hidden(D_433,B_435)
      | k1_relset_1(B_435,A_434,'#skF_6') != B_435
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(B_435,A_434))) ) ),
    inference(resolution,[status(thm)],[c_1093,c_2195])).

tff(c_2213,plain,(
    ! [D_436,B_437,A_438] :
      ( ~ r2_hidden(D_436,B_437)
      | k1_relset_1(B_437,A_438,'#skF_6') != B_437 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1092,c_2207])).

tff(c_2235,plain,(
    ! [A_439,A_440,B_441] :
      ( k1_relset_1(A_439,A_440,'#skF_6') != A_439
      | r1_tarski(A_439,B_441) ) ),
    inference(resolution,[status(thm)],[c_6,c_2213])).

tff(c_2246,plain,(
    ! [B_442] : r1_tarski(k1_tarski('#skF_4'),B_442) ),
    inference(superposition,[status(thm),theory(equality)],[c_1612,c_2235])).

tff(c_1123,plain,(
    ! [B_239,A_240] :
      ( B_239 = A_240
      | ~ r1_tarski(B_239,A_240)
      | ~ r1_tarski(A_240,B_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1132,plain,(
    ! [A_8] :
      ( A_8 = '#skF_6'
      | ~ r1_tarski(A_8,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1093,c_1123])).

tff(c_2306,plain,(
    k1_tarski('#skF_4') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_2246,c_1132])).

tff(c_2339,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1436,c_2306])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:23:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.47/1.82  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.47/1.82  
% 4.47/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.47/1.83  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 4.47/1.83  
% 4.47/1.83  %Foreground sorts:
% 4.47/1.83  
% 4.47/1.83  
% 4.47/1.83  %Background operators:
% 4.47/1.83  
% 4.47/1.83  
% 4.47/1.83  %Foreground operators:
% 4.47/1.83  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.47/1.83  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.47/1.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.47/1.83  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.47/1.83  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.47/1.83  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.47/1.83  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.47/1.83  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.47/1.83  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.47/1.83  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.47/1.83  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.47/1.83  tff('#skF_5', type, '#skF_5': $i).
% 4.47/1.83  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.47/1.83  tff('#skF_6', type, '#skF_6': $i).
% 4.47/1.83  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.47/1.83  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.47/1.83  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.47/1.83  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.47/1.83  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.47/1.83  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.47/1.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.47/1.83  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.47/1.83  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.47/1.83  tff('#skF_4', type, '#skF_4': $i).
% 4.47/1.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.47/1.83  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.47/1.83  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 4.47/1.83  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.47/1.83  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.47/1.83  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.47/1.83  
% 4.47/1.84  tff(f_152, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 4.47/1.84  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.47/1.84  tff(f_83, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 4.47/1.84  tff(f_91, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 4.47/1.84  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.47/1.84  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.47/1.84  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 4.47/1.84  tff(f_42, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.47/1.84  tff(f_61, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 4.47/1.84  tff(f_63, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 4.47/1.84  tff(f_140, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.47/1.84  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.47/1.84  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.47/1.84  tff(f_122, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relset_1)).
% 4.47/1.84  tff(f_96, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.47/1.84  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.47/1.84  tff(c_78, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.47/1.84  tff(c_135, plain, (![C_73, A_74, B_75]: (v1_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.47/1.84  tff(c_143, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_78, c_135])).
% 4.47/1.84  tff(c_82, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.47/1.84  tff(c_42, plain, (![A_24]: (k1_relat_1(A_24)!=k1_xboole_0 | k1_xboole_0=A_24 | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.47/1.84  tff(c_152, plain, (k1_relat_1('#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_143, c_42])).
% 4.47/1.84  tff(c_164, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_152])).
% 4.47/1.84  tff(c_415, plain, (![B_129, A_130]: (k1_tarski(k1_funct_1(B_129, A_130))=k2_relat_1(B_129) | k1_tarski(A_130)!=k1_relat_1(B_129) | ~v1_funct_1(B_129) | ~v1_relat_1(B_129))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.47/1.84  tff(c_308, plain, (![A_109, B_110, C_111]: (k2_relset_1(A_109, B_110, C_111)=k2_relat_1(C_111) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.47/1.84  tff(c_316, plain, (k2_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_78, c_308])).
% 4.47/1.84  tff(c_74, plain, (k2_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')!=k1_tarski(k1_funct_1('#skF_6', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.47/1.84  tff(c_325, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_4'))!=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_316, c_74])).
% 4.47/1.84  tff(c_424, plain, (k1_tarski('#skF_4')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_415, c_325])).
% 4.47/1.84  tff(c_440, plain, (k1_tarski('#skF_4')!=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_143, c_82, c_424])).
% 4.47/1.84  tff(c_251, plain, (![C_97, A_98, B_99]: (v4_relat_1(C_97, A_98) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.47/1.84  tff(c_259, plain, (v4_relat_1('#skF_6', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_78, c_251])).
% 4.47/1.84  tff(c_38, plain, (![B_23, A_22]: (r1_tarski(k1_relat_1(B_23), A_22) | ~v4_relat_1(B_23, A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.47/1.84  tff(c_16, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.47/1.84  tff(c_825, plain, (![B_186, C_187, A_188]: (k2_tarski(B_186, C_187)=A_188 | k1_tarski(C_187)=A_188 | k1_tarski(B_186)=A_188 | k1_xboole_0=A_188 | ~r1_tarski(A_188, k2_tarski(B_186, C_187)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.47/1.84  tff(c_842, plain, (![A_9, A_188]: (k2_tarski(A_9, A_9)=A_188 | k1_tarski(A_9)=A_188 | k1_tarski(A_9)=A_188 | k1_xboole_0=A_188 | ~r1_tarski(A_188, k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_825])).
% 4.47/1.84  tff(c_1043, plain, (![A_231, A_232]: (k1_tarski(A_231)=A_232 | k1_tarski(A_231)=A_232 | k1_tarski(A_231)=A_232 | k1_xboole_0=A_232 | ~r1_tarski(A_232, k1_tarski(A_231)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_842])).
% 4.47/1.84  tff(c_1069, plain, (![A_233, B_234]: (k1_tarski(A_233)=k1_relat_1(B_234) | k1_relat_1(B_234)=k1_xboole_0 | ~v4_relat_1(B_234, k1_tarski(A_233)) | ~v1_relat_1(B_234))), inference(resolution, [status(thm)], [c_38, c_1043])).
% 4.47/1.84  tff(c_1075, plain, (k1_tarski('#skF_4')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_259, c_1069])).
% 4.47/1.84  tff(c_1082, plain, (k1_tarski('#skF_4')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_143, c_1075])).
% 4.47/1.84  tff(c_1084, plain, $false, inference(negUnitSimplification, [status(thm)], [c_164, c_440, c_1082])).
% 4.47/1.84  tff(c_1085, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_152])).
% 4.47/1.84  tff(c_1086, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_152])).
% 4.47/1.84  tff(c_1100, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1085, c_1086])).
% 4.47/1.84  tff(c_1411, plain, (![B_297, A_298]: (k1_tarski(k1_funct_1(B_297, A_298))=k2_relat_1(B_297) | k1_tarski(A_298)!=k1_relat_1(B_297) | ~v1_funct_1(B_297) | ~v1_relat_1(B_297))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.47/1.84  tff(c_32, plain, (![A_18]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.47/1.84  tff(c_1092, plain, (![A_18]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_18)))), inference(demodulation, [status(thm), theory('equality')], [c_1085, c_32])).
% 4.47/1.84  tff(c_1295, plain, (![A_280, B_281, C_282]: (k2_relset_1(A_280, B_281, C_282)=k2_relat_1(C_282) | ~m1_subset_1(C_282, k1_zfmisc_1(k2_zfmisc_1(A_280, B_281))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.47/1.84  tff(c_1300, plain, (![A_280, B_281]: (k2_relset_1(A_280, B_281, '#skF_6')=k2_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_1092, c_1295])).
% 4.47/1.84  tff(c_1316, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_4'))!=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1300, c_74])).
% 4.47/1.84  tff(c_1417, plain, (k1_tarski('#skF_4')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1411, c_1316])).
% 4.47/1.84  tff(c_1436, plain, (k1_tarski('#skF_4')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_143, c_82, c_1100, c_1417])).
% 4.47/1.84  tff(c_76, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.47/1.84  tff(c_1094, plain, ('#skF_5'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1085, c_76])).
% 4.47/1.84  tff(c_80, plain, (v1_funct_2('#skF_6', k1_tarski('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.47/1.84  tff(c_72, plain, (![B_52, A_51, C_53]: (k1_xboole_0=B_52 | k1_relset_1(A_51, B_52, C_53)=A_51 | ~v1_funct_2(C_53, A_51, B_52) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_140])).
% 4.47/1.84  tff(c_1591, plain, (![B_330, A_331, C_332]: (B_330='#skF_6' | k1_relset_1(A_331, B_330, C_332)=A_331 | ~v1_funct_2(C_332, A_331, B_330) | ~m1_subset_1(C_332, k1_zfmisc_1(k2_zfmisc_1(A_331, B_330))))), inference(demodulation, [status(thm), theory('equality')], [c_1085, c_72])).
% 4.47/1.84  tff(c_1597, plain, (![B_333, A_334]: (B_333='#skF_6' | k1_relset_1(A_334, B_333, '#skF_6')=A_334 | ~v1_funct_2('#skF_6', A_334, B_333))), inference(resolution, [status(thm)], [c_1092, c_1591])).
% 4.47/1.84  tff(c_1606, plain, ('#skF_5'='#skF_6' | k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_tarski('#skF_4')), inference(resolution, [status(thm)], [c_80, c_1597])).
% 4.47/1.84  tff(c_1612, plain, (k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_1094, c_1606])).
% 4.47/1.84  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.47/1.84  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.47/1.84  tff(c_1093, plain, (![A_8]: (r1_tarski('#skF_6', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_1085, c_14])).
% 4.47/1.84  tff(c_1915, plain, (![D_391, A_392, B_393, C_394]: (r2_hidden(k4_tarski(D_391, '#skF_3'(A_392, B_393, C_394, D_391)), C_394) | ~r2_hidden(D_391, B_393) | k1_relset_1(B_393, A_392, C_394)!=B_393 | ~m1_subset_1(C_394, k1_zfmisc_1(k2_zfmisc_1(B_393, A_392))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.47/1.84  tff(c_46, plain, (![B_28, A_27]: (~r1_tarski(B_28, A_27) | ~r2_hidden(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.47/1.84  tff(c_2195, plain, (![C_432, D_433, A_434, B_435]: (~r1_tarski(C_432, k4_tarski(D_433, '#skF_3'(A_434, B_435, C_432, D_433))) | ~r2_hidden(D_433, B_435) | k1_relset_1(B_435, A_434, C_432)!=B_435 | ~m1_subset_1(C_432, k1_zfmisc_1(k2_zfmisc_1(B_435, A_434))))), inference(resolution, [status(thm)], [c_1915, c_46])).
% 4.47/1.84  tff(c_2207, plain, (![D_433, B_435, A_434]: (~r2_hidden(D_433, B_435) | k1_relset_1(B_435, A_434, '#skF_6')!=B_435 | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(B_435, A_434))))), inference(resolution, [status(thm)], [c_1093, c_2195])).
% 4.47/1.84  tff(c_2213, plain, (![D_436, B_437, A_438]: (~r2_hidden(D_436, B_437) | k1_relset_1(B_437, A_438, '#skF_6')!=B_437)), inference(demodulation, [status(thm), theory('equality')], [c_1092, c_2207])).
% 4.47/1.84  tff(c_2235, plain, (![A_439, A_440, B_441]: (k1_relset_1(A_439, A_440, '#skF_6')!=A_439 | r1_tarski(A_439, B_441))), inference(resolution, [status(thm)], [c_6, c_2213])).
% 4.47/1.84  tff(c_2246, plain, (![B_442]: (r1_tarski(k1_tarski('#skF_4'), B_442))), inference(superposition, [status(thm), theory('equality')], [c_1612, c_2235])).
% 4.47/1.84  tff(c_1123, plain, (![B_239, A_240]: (B_239=A_240 | ~r1_tarski(B_239, A_240) | ~r1_tarski(A_240, B_239))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.47/1.84  tff(c_1132, plain, (![A_8]: (A_8='#skF_6' | ~r1_tarski(A_8, '#skF_6'))), inference(resolution, [status(thm)], [c_1093, c_1123])).
% 4.47/1.84  tff(c_2306, plain, (k1_tarski('#skF_4')='#skF_6'), inference(resolution, [status(thm)], [c_2246, c_1132])).
% 4.47/1.84  tff(c_2339, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1436, c_2306])).
% 4.47/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.47/1.84  
% 4.47/1.84  Inference rules
% 4.47/1.84  ----------------------
% 4.47/1.84  #Ref     : 0
% 4.47/1.84  #Sup     : 473
% 4.47/1.84  #Fact    : 0
% 4.47/1.84  #Define  : 0
% 4.47/1.84  #Split   : 3
% 4.47/1.84  #Chain   : 0
% 4.47/1.84  #Close   : 0
% 4.47/1.84  
% 4.47/1.84  Ordering : KBO
% 4.47/1.84  
% 4.47/1.84  Simplification rules
% 4.47/1.84  ----------------------
% 4.47/1.84  #Subsume      : 85
% 4.47/1.84  #Demod        : 217
% 4.47/1.84  #Tautology    : 169
% 4.47/1.84  #SimpNegUnit  : 9
% 4.47/1.84  #BackRed      : 12
% 4.47/1.84  
% 4.47/1.84  #Partial instantiations: 0
% 4.47/1.84  #Strategies tried      : 1
% 4.47/1.84  
% 4.47/1.84  Timing (in seconds)
% 4.47/1.84  ----------------------
% 4.47/1.85  Preprocessing        : 0.37
% 4.47/1.85  Parsing              : 0.19
% 4.47/1.85  CNF conversion       : 0.03
% 4.47/1.85  Main loop            : 0.64
% 4.47/1.85  Inferencing          : 0.24
% 4.47/1.85  Reduction            : 0.18
% 4.47/1.85  Demodulation         : 0.12
% 4.47/1.85  BG Simplification    : 0.03
% 4.47/1.85  Subsumption          : 0.14
% 4.47/1.85  Abstraction          : 0.03
% 4.47/1.85  MUC search           : 0.00
% 4.47/1.85  Cooper               : 0.00
% 4.47/1.85  Total                : 1.04
% 4.47/1.85  Index Insertion      : 0.00
% 4.47/1.85  Index Deletion       : 0.00
% 4.47/1.85  Index Matching       : 0.00
% 4.47/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
