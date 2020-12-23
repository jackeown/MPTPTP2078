%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:28 EST 2020

% Result     : Theorem 4.60s
% Output     : CNFRefutation 4.89s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 226 expanded)
%              Number of leaves         :   45 (  94 expanded)
%              Depth                    :   11
%              Number of atoms          :  157 ( 456 expanded)
%              Number of equality atoms :   69 ( 193 expanded)
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

tff(f_143,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_54,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_131,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_113,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
      <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_74,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_109,plain,(
    ! [C_64,A_65,B_66] :
      ( v1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_117,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_109])).

tff(c_78,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_38,plain,(
    ! [A_23] :
      ( k1_relat_1(A_23) != k1_xboole_0
      | k1_xboole_0 = A_23
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_126,plain,
    ( k1_relat_1('#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_117,c_38])).

tff(c_160,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_364,plain,(
    ! [B_115,A_116] :
      ( k1_tarski(k1_funct_1(B_115,A_116)) = k2_relat_1(B_115)
      | k1_tarski(A_116) != k1_relat_1(B_115)
      | ~ v1_funct_1(B_115)
      | ~ v1_relat_1(B_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_337,plain,(
    ! [A_110,B_111,C_112] :
      ( k2_relset_1(A_110,B_111,C_112) = k2_relat_1(C_112)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_350,plain,(
    k2_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_337])).

tff(c_70,plain,(
    k2_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') != k1_tarski(k1_funct_1('#skF_6','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_359,plain,(
    k1_tarski(k1_funct_1('#skF_6','#skF_4')) != k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_350,c_70])).

tff(c_370,plain,
    ( k1_tarski('#skF_4') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_364,c_359])).

tff(c_380,plain,(
    k1_tarski('#skF_4') != k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_78,c_370])).

tff(c_249,plain,(
    ! [C_94,A_95,B_96] :
      ( v4_relat_1(C_94,A_95)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_257,plain,(
    v4_relat_1('#skF_6',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_74,c_249])).

tff(c_34,plain,(
    ! [B_22,A_21] :
      ( r1_tarski(k1_relat_1(B_22),A_21)
      | ~ v4_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_222,plain,(
    ! [B_89,A_90] :
      ( k1_tarski(B_89) = A_90
      | k1_xboole_0 = A_90
      | ~ r1_tarski(A_90,k1_tarski(B_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_586,plain,(
    ! [B_145,B_146] :
      ( k1_tarski(B_145) = k1_relat_1(B_146)
      | k1_relat_1(B_146) = k1_xboole_0
      | ~ v4_relat_1(B_146,k1_tarski(B_145))
      | ~ v1_relat_1(B_146) ) ),
    inference(resolution,[status(thm)],[c_34,c_222])).

tff(c_592,plain,
    ( k1_tarski('#skF_4') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_257,c_586])).

tff(c_599,plain,
    ( k1_tarski('#skF_4') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_592])).

tff(c_601,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_380,c_599])).

tff(c_602,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_603,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_621,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_602,c_603])).

tff(c_801,plain,(
    ! [B_191,A_192] :
      ( k1_tarski(k1_funct_1(B_191,A_192)) = k2_relat_1(B_191)
      | k1_tarski(A_192) != k1_relat_1(B_191)
      | ~ v1_funct_1(B_191)
      | ~ v1_relat_1(B_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_28,plain,(
    ! [A_17] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_609,plain,(
    ! [A_17] : m1_subset_1('#skF_6',k1_zfmisc_1(A_17)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_602,c_28])).

tff(c_781,plain,(
    ! [A_184,B_185,C_186] :
      ( k2_relset_1(A_184,B_185,C_186) = k2_relat_1(C_186)
      | ~ m1_subset_1(C_186,k1_zfmisc_1(k2_zfmisc_1(A_184,B_185))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_786,plain,(
    ! [A_184,B_185] : k2_relset_1(A_184,B_185,'#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_609,c_781])).

tff(c_793,plain,(
    k1_tarski(k1_funct_1('#skF_6','#skF_4')) != k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_786,c_70])).

tff(c_807,plain,
    ( k1_tarski('#skF_4') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_801,c_793])).

tff(c_817,plain,(
    k1_tarski('#skF_4') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_78,c_621,c_807])).

tff(c_72,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_611,plain,(
    '#skF_5' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_602,c_72])).

tff(c_76,plain,(
    v1_funct_2('#skF_6',k1_tarski('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_68,plain,(
    ! [B_51,A_50,C_52] :
      ( k1_xboole_0 = B_51
      | k1_relset_1(A_50,B_51,C_52) = A_50
      | ~ v1_funct_2(C_52,A_50,B_51)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1067,plain,(
    ! [B_231,A_232,C_233] :
      ( B_231 = '#skF_6'
      | k1_relset_1(A_232,B_231,C_233) = A_232
      | ~ v1_funct_2(C_233,A_232,B_231)
      | ~ m1_subset_1(C_233,k1_zfmisc_1(k2_zfmisc_1(A_232,B_231))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_602,c_68])).

tff(c_1073,plain,(
    ! [B_234,A_235] :
      ( B_234 = '#skF_6'
      | k1_relset_1(A_235,B_234,'#skF_6') = A_235
      | ~ v1_funct_2('#skF_6',A_235,B_234) ) ),
    inference(resolution,[status(thm)],[c_609,c_1067])).

tff(c_1082,plain,
    ( '#skF_5' = '#skF_6'
    | k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_tarski('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_1073])).

tff(c_1088,plain,(
    k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_611,c_1082])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_610,plain,(
    ! [A_8] : r1_tarski('#skF_6',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_602,c_14])).

tff(c_1281,plain,(
    ! [D_266,A_267,B_268,C_269] :
      ( r2_hidden(k4_tarski(D_266,'#skF_3'(A_267,B_268,C_269,D_266)),C_269)
      | ~ r2_hidden(D_266,B_268)
      | k1_relset_1(B_268,A_267,C_269) != B_268
      | ~ m1_subset_1(C_269,k1_zfmisc_1(k2_zfmisc_1(B_268,A_267))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_42,plain,(
    ! [B_27,A_26] :
      ( ~ r1_tarski(B_27,A_26)
      | ~ r2_hidden(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1388,plain,(
    ! [C_280,D_281,A_282,B_283] :
      ( ~ r1_tarski(C_280,k4_tarski(D_281,'#skF_3'(A_282,B_283,C_280,D_281)))
      | ~ r2_hidden(D_281,B_283)
      | k1_relset_1(B_283,A_282,C_280) != B_283
      | ~ m1_subset_1(C_280,k1_zfmisc_1(k2_zfmisc_1(B_283,A_282))) ) ),
    inference(resolution,[status(thm)],[c_1281,c_42])).

tff(c_1400,plain,(
    ! [D_281,B_283,A_282] :
      ( ~ r2_hidden(D_281,B_283)
      | k1_relset_1(B_283,A_282,'#skF_6') != B_283
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(B_283,A_282))) ) ),
    inference(resolution,[status(thm)],[c_610,c_1388])).

tff(c_1406,plain,(
    ! [D_284,B_285,A_286] :
      ( ~ r2_hidden(D_284,B_285)
      | k1_relset_1(B_285,A_286,'#skF_6') != B_285 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_609,c_1400])).

tff(c_1422,plain,(
    ! [A_287,A_288,B_289] :
      ( k1_relset_1(A_287,A_288,'#skF_6') != A_287
      | r1_tarski(A_287,B_289) ) ),
    inference(resolution,[status(thm)],[c_6,c_1406])).

tff(c_1433,plain,(
    ! [B_290] : r1_tarski(k1_tarski('#skF_4'),B_290) ),
    inference(superposition,[status(thm),theory(equality)],[c_1088,c_1422])).

tff(c_127,plain,(
    ! [B_67,A_68] :
      ( B_67 = A_68
      | ~ r1_tarski(B_67,A_68)
      | ~ r1_tarski(A_68,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_136,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_127])).

tff(c_604,plain,(
    ! [A_8] :
      ( A_8 = '#skF_6'
      | ~ r1_tarski(A_8,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_602,c_602,c_136])).

tff(c_1473,plain,(
    k1_tarski('#skF_4') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1433,c_604])).

tff(c_1494,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_817,c_1473])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:53:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.60/2.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.60/2.21  
% 4.60/2.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.60/2.21  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 4.60/2.21  
% 4.60/2.21  %Foreground sorts:
% 4.60/2.21  
% 4.60/2.21  
% 4.60/2.21  %Background operators:
% 4.60/2.21  
% 4.60/2.21  
% 4.60/2.21  %Foreground operators:
% 4.60/2.21  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.60/2.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.60/2.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.60/2.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.60/2.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.60/2.21  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.60/2.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.60/2.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.60/2.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.60/2.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.60/2.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.60/2.21  tff('#skF_5', type, '#skF_5': $i).
% 4.60/2.21  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.60/2.21  tff('#skF_6', type, '#skF_6': $i).
% 4.60/2.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.60/2.21  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.60/2.21  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.60/2.21  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.60/2.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.60/2.21  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.60/2.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.60/2.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.60/2.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.60/2.21  tff('#skF_4', type, '#skF_4': $i).
% 4.60/2.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.60/2.21  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.60/2.21  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 4.60/2.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.60/2.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.60/2.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.60/2.21  
% 4.89/2.24  tff(f_143, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_2)).
% 4.89/2.24  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.89/2.24  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 4.89/2.24  tff(f_82, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 4.89/2.24  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.89/2.24  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.89/2.24  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 4.89/2.24  tff(f_52, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 4.89/2.24  tff(f_54, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.89/2.24  tff(f_131, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.89/2.24  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.89/2.24  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.89/2.24  tff(f_113, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relset_1)).
% 4.89/2.24  tff(f_87, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.89/2.24  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.89/2.24  tff(c_74, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.89/2.24  tff(c_109, plain, (![C_64, A_65, B_66]: (v1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.89/2.24  tff(c_117, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_74, c_109])).
% 4.89/2.24  tff(c_78, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.89/2.24  tff(c_38, plain, (![A_23]: (k1_relat_1(A_23)!=k1_xboole_0 | k1_xboole_0=A_23 | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.89/2.24  tff(c_126, plain, (k1_relat_1('#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_117, c_38])).
% 4.89/2.24  tff(c_160, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_126])).
% 4.89/2.24  tff(c_364, plain, (![B_115, A_116]: (k1_tarski(k1_funct_1(B_115, A_116))=k2_relat_1(B_115) | k1_tarski(A_116)!=k1_relat_1(B_115) | ~v1_funct_1(B_115) | ~v1_relat_1(B_115))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.89/2.24  tff(c_337, plain, (![A_110, B_111, C_112]: (k2_relset_1(A_110, B_111, C_112)=k2_relat_1(C_112) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.89/2.24  tff(c_350, plain, (k2_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_74, c_337])).
% 4.89/2.24  tff(c_70, plain, (k2_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')!=k1_tarski(k1_funct_1('#skF_6', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.89/2.24  tff(c_359, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_4'))!=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_350, c_70])).
% 4.89/2.24  tff(c_370, plain, (k1_tarski('#skF_4')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_364, c_359])).
% 4.89/2.24  tff(c_380, plain, (k1_tarski('#skF_4')!=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_117, c_78, c_370])).
% 4.89/2.24  tff(c_249, plain, (![C_94, A_95, B_96]: (v4_relat_1(C_94, A_95) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.89/2.24  tff(c_257, plain, (v4_relat_1('#skF_6', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_74, c_249])).
% 4.89/2.24  tff(c_34, plain, (![B_22, A_21]: (r1_tarski(k1_relat_1(B_22), A_21) | ~v4_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.89/2.24  tff(c_222, plain, (![B_89, A_90]: (k1_tarski(B_89)=A_90 | k1_xboole_0=A_90 | ~r1_tarski(A_90, k1_tarski(B_89)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.89/2.24  tff(c_586, plain, (![B_145, B_146]: (k1_tarski(B_145)=k1_relat_1(B_146) | k1_relat_1(B_146)=k1_xboole_0 | ~v4_relat_1(B_146, k1_tarski(B_145)) | ~v1_relat_1(B_146))), inference(resolution, [status(thm)], [c_34, c_222])).
% 4.89/2.24  tff(c_592, plain, (k1_tarski('#skF_4')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_257, c_586])).
% 4.89/2.24  tff(c_599, plain, (k1_tarski('#skF_4')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_117, c_592])).
% 4.89/2.24  tff(c_601, plain, $false, inference(negUnitSimplification, [status(thm)], [c_160, c_380, c_599])).
% 4.89/2.24  tff(c_602, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_126])).
% 4.89/2.24  tff(c_603, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_126])).
% 4.89/2.24  tff(c_621, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_602, c_603])).
% 4.89/2.24  tff(c_801, plain, (![B_191, A_192]: (k1_tarski(k1_funct_1(B_191, A_192))=k2_relat_1(B_191) | k1_tarski(A_192)!=k1_relat_1(B_191) | ~v1_funct_1(B_191) | ~v1_relat_1(B_191))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.89/2.24  tff(c_28, plain, (![A_17]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.89/2.24  tff(c_609, plain, (![A_17]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_17)))), inference(demodulation, [status(thm), theory('equality')], [c_602, c_28])).
% 4.89/2.24  tff(c_781, plain, (![A_184, B_185, C_186]: (k2_relset_1(A_184, B_185, C_186)=k2_relat_1(C_186) | ~m1_subset_1(C_186, k1_zfmisc_1(k2_zfmisc_1(A_184, B_185))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.89/2.24  tff(c_786, plain, (![A_184, B_185]: (k2_relset_1(A_184, B_185, '#skF_6')=k2_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_609, c_781])).
% 4.89/2.24  tff(c_793, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_4'))!=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_786, c_70])).
% 4.89/2.24  tff(c_807, plain, (k1_tarski('#skF_4')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_801, c_793])).
% 4.89/2.24  tff(c_817, plain, (k1_tarski('#skF_4')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_117, c_78, c_621, c_807])).
% 4.89/2.24  tff(c_72, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.89/2.24  tff(c_611, plain, ('#skF_5'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_602, c_72])).
% 4.89/2.24  tff(c_76, plain, (v1_funct_2('#skF_6', k1_tarski('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.89/2.24  tff(c_68, plain, (![B_51, A_50, C_52]: (k1_xboole_0=B_51 | k1_relset_1(A_50, B_51, C_52)=A_50 | ~v1_funct_2(C_52, A_50, B_51) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.89/2.24  tff(c_1067, plain, (![B_231, A_232, C_233]: (B_231='#skF_6' | k1_relset_1(A_232, B_231, C_233)=A_232 | ~v1_funct_2(C_233, A_232, B_231) | ~m1_subset_1(C_233, k1_zfmisc_1(k2_zfmisc_1(A_232, B_231))))), inference(demodulation, [status(thm), theory('equality')], [c_602, c_68])).
% 4.89/2.24  tff(c_1073, plain, (![B_234, A_235]: (B_234='#skF_6' | k1_relset_1(A_235, B_234, '#skF_6')=A_235 | ~v1_funct_2('#skF_6', A_235, B_234))), inference(resolution, [status(thm)], [c_609, c_1067])).
% 4.89/2.24  tff(c_1082, plain, ('#skF_5'='#skF_6' | k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_tarski('#skF_4')), inference(resolution, [status(thm)], [c_76, c_1073])).
% 4.89/2.24  tff(c_1088, plain, (k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_611, c_1082])).
% 4.89/2.24  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.89/2.24  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.89/2.24  tff(c_610, plain, (![A_8]: (r1_tarski('#skF_6', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_602, c_14])).
% 4.89/2.24  tff(c_1281, plain, (![D_266, A_267, B_268, C_269]: (r2_hidden(k4_tarski(D_266, '#skF_3'(A_267, B_268, C_269, D_266)), C_269) | ~r2_hidden(D_266, B_268) | k1_relset_1(B_268, A_267, C_269)!=B_268 | ~m1_subset_1(C_269, k1_zfmisc_1(k2_zfmisc_1(B_268, A_267))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.89/2.24  tff(c_42, plain, (![B_27, A_26]: (~r1_tarski(B_27, A_26) | ~r2_hidden(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.89/2.24  tff(c_1388, plain, (![C_280, D_281, A_282, B_283]: (~r1_tarski(C_280, k4_tarski(D_281, '#skF_3'(A_282, B_283, C_280, D_281))) | ~r2_hidden(D_281, B_283) | k1_relset_1(B_283, A_282, C_280)!=B_283 | ~m1_subset_1(C_280, k1_zfmisc_1(k2_zfmisc_1(B_283, A_282))))), inference(resolution, [status(thm)], [c_1281, c_42])).
% 4.89/2.24  tff(c_1400, plain, (![D_281, B_283, A_282]: (~r2_hidden(D_281, B_283) | k1_relset_1(B_283, A_282, '#skF_6')!=B_283 | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(B_283, A_282))))), inference(resolution, [status(thm)], [c_610, c_1388])).
% 4.89/2.24  tff(c_1406, plain, (![D_284, B_285, A_286]: (~r2_hidden(D_284, B_285) | k1_relset_1(B_285, A_286, '#skF_6')!=B_285)), inference(demodulation, [status(thm), theory('equality')], [c_609, c_1400])).
% 4.89/2.24  tff(c_1422, plain, (![A_287, A_288, B_289]: (k1_relset_1(A_287, A_288, '#skF_6')!=A_287 | r1_tarski(A_287, B_289))), inference(resolution, [status(thm)], [c_6, c_1406])).
% 4.89/2.24  tff(c_1433, plain, (![B_290]: (r1_tarski(k1_tarski('#skF_4'), B_290))), inference(superposition, [status(thm), theory('equality')], [c_1088, c_1422])).
% 4.89/2.24  tff(c_127, plain, (![B_67, A_68]: (B_67=A_68 | ~r1_tarski(B_67, A_68) | ~r1_tarski(A_68, B_67))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.89/2.24  tff(c_136, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_127])).
% 4.89/2.24  tff(c_604, plain, (![A_8]: (A_8='#skF_6' | ~r1_tarski(A_8, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_602, c_602, c_136])).
% 4.89/2.24  tff(c_1473, plain, (k1_tarski('#skF_4')='#skF_6'), inference(resolution, [status(thm)], [c_1433, c_604])).
% 4.89/2.24  tff(c_1494, plain, $false, inference(negUnitSimplification, [status(thm)], [c_817, c_1473])).
% 4.89/2.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.89/2.24  
% 4.89/2.24  Inference rules
% 4.89/2.24  ----------------------
% 4.89/2.24  #Ref     : 0
% 4.89/2.24  #Sup     : 277
% 4.89/2.24  #Fact    : 0
% 4.89/2.24  #Define  : 0
% 4.89/2.24  #Split   : 2
% 4.89/2.24  #Chain   : 0
% 4.89/2.24  #Close   : 0
% 4.89/2.24  
% 4.89/2.24  Ordering : KBO
% 4.89/2.24  
% 4.89/2.24  Simplification rules
% 4.89/2.24  ----------------------
% 4.89/2.24  #Subsume      : 45
% 4.89/2.24  #Demod        : 159
% 4.89/2.24  #Tautology    : 109
% 4.89/2.24  #SimpNegUnit  : 4
% 4.89/2.24  #BackRed      : 11
% 4.89/2.24  
% 4.89/2.24  #Partial instantiations: 0
% 4.89/2.24  #Strategies tried      : 1
% 4.89/2.24  
% 4.89/2.24  Timing (in seconds)
% 4.89/2.24  ----------------------
% 4.89/2.25  Preprocessing        : 0.57
% 4.89/2.25  Parsing              : 0.29
% 4.89/2.25  CNF conversion       : 0.04
% 4.89/2.25  Main loop            : 0.79
% 4.89/2.25  Inferencing          : 0.29
% 4.89/2.25  Reduction            : 0.23
% 4.89/2.25  Demodulation         : 0.16
% 4.89/2.25  BG Simplification    : 0.04
% 4.89/2.25  Subsumption          : 0.16
% 4.89/2.25  Abstraction          : 0.04
% 4.89/2.25  MUC search           : 0.00
% 4.89/2.25  Cooper               : 0.00
% 4.89/2.25  Total                : 1.42
% 4.89/2.25  Index Insertion      : 0.00
% 4.89/2.25  Index Deletion       : 0.00
% 4.89/2.25  Index Matching       : 0.00
% 4.89/2.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
