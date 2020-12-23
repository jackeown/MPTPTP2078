%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:42 EST 2020

% Result     : Theorem 3.80s
% Output     : CNFRefutation 3.94s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 285 expanded)
%              Number of leaves         :   34 ( 110 expanded)
%              Depth                    :   13
%              Number of atoms          :  216 ( 955 expanded)
%              Number of equality atoms :   53 ( 237 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_102,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( v2_funct_1(B)
        <=> ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A)
                & k1_funct_1(B,C) = k1_funct_1(B,D) )
             => C = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_funct_2)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_53,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
      <=> ! [B,C] :
            ( ( r2_hidden(B,k1_relat_1(A))
              & r2_hidden(C,k1_relat_1(A))
              & k1_funct_1(A,B) = k1_funct_1(A,C) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

tff(f_84,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(D)
          & r2_hidden(C,A) )
       => ( B = k1_xboole_0
          | k1_funct_1(k2_funct_1(D),k1_funct_1(D,C)) = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1390,plain,(
    ! [A_188,B_189] :
      ( ~ r2_hidden('#skF_1'(A_188,B_189),B_189)
      | r1_tarski(A_188,B_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1395,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_1390])).

tff(c_38,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_36,plain,(
    v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_40,plain,
    ( '#skF_7' != '#skF_6'
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_60,plain,(
    ~ v2_funct_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_83,plain,(
    ! [C_48,A_49,B_50] :
      ( v1_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_92,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_83])).

tff(c_189,plain,(
    ! [A_77,B_78,C_79] :
      ( k1_relset_1(A_77,B_78,C_79) = k1_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_198,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_189])).

tff(c_235,plain,(
    ! [A_87,B_88,C_89] :
      ( m1_subset_1(k1_relset_1(A_87,B_88,C_89),k1_zfmisc_1(A_87))
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_255,plain,
    ( m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_235])).

tff(c_260,plain,(
    m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_255])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_264,plain,(
    r1_tarski(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_260,c_10])).

tff(c_130,plain,(
    ! [A_63] :
      ( r2_hidden('#skF_3'(A_63),k1_relat_1(A_63))
      | v2_funct_1(A_63)
      | ~ v1_funct_1(A_63)
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1316,plain,(
    ! [A_172,B_173] :
      ( r2_hidden('#skF_3'(A_172),B_173)
      | ~ r1_tarski(k1_relat_1(A_172),B_173)
      | v2_funct_1(A_172)
      | ~ v1_funct_1(A_172)
      | ~ v1_relat_1(A_172) ) ),
    inference(resolution,[status(thm)],[c_130,c_2])).

tff(c_123,plain,(
    ! [A_62] :
      ( '#skF_2'(A_62) != '#skF_3'(A_62)
      | v2_funct_1(A_62)
      | ~ v1_funct_1(A_62)
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_126,plain,
    ( '#skF_2'('#skF_5') != '#skF_3'('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_123,c_60])).

tff(c_129,plain,(
    '#skF_2'('#skF_5') != '#skF_3'('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_38,c_126])).

tff(c_138,plain,(
    ! [A_64] :
      ( r2_hidden('#skF_2'(A_64),k1_relat_1(A_64))
      | v2_funct_1(A_64)
      | ~ v1_funct_1(A_64)
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_825,plain,(
    ! [A_132,B_133] :
      ( r2_hidden('#skF_2'(A_132),B_133)
      | ~ r1_tarski(k1_relat_1(A_132),B_133)
      | v2_funct_1(A_132)
      | ~ v1_funct_1(A_132)
      | ~ v1_relat_1(A_132) ) ),
    inference(resolution,[status(thm)],[c_138,c_2])).

tff(c_272,plain,(
    ! [A_92] :
      ( k1_funct_1(A_92,'#skF_2'(A_92)) = k1_funct_1(A_92,'#skF_3'(A_92))
      | v2_funct_1(A_92)
      | ~ v1_funct_1(A_92)
      | ~ v1_relat_1(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_58,plain,(
    ! [D_36,C_35] :
      ( v2_funct_1('#skF_5')
      | D_36 = C_35
      | k1_funct_1('#skF_5',D_36) != k1_funct_1('#skF_5',C_35)
      | ~ r2_hidden(D_36,'#skF_4')
      | ~ r2_hidden(C_35,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_146,plain,(
    ! [D_36,C_35] :
      ( D_36 = C_35
      | k1_funct_1('#skF_5',D_36) != k1_funct_1('#skF_5',C_35)
      | ~ r2_hidden(D_36,'#skF_4')
      | ~ r2_hidden(C_35,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_58])).

tff(c_281,plain,(
    ! [D_36] :
      ( D_36 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',D_36) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden(D_36,'#skF_4')
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_146])).

tff(c_290,plain,(
    ! [D_36] :
      ( D_36 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',D_36) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden(D_36,'#skF_4')
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | v2_funct_1('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_38,c_281])).

tff(c_291,plain,(
    ! [D_36] :
      ( D_36 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',D_36) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden(D_36,'#skF_4')
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_290])).

tff(c_442,plain,(
    ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_291])).

tff(c_830,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4')
    | v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_825,c_442])).

tff(c_839,plain,(
    v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_38,c_264,c_830])).

tff(c_841,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_839])).

tff(c_843,plain,(
    r2_hidden('#skF_2'('#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_291])).

tff(c_278,plain,(
    ! [C_35] :
      ( C_35 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',C_35) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | ~ r2_hidden(C_35,'#skF_4')
      | v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_146])).

tff(c_287,plain,(
    ! [C_35] :
      ( C_35 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',C_35) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | ~ r2_hidden(C_35,'#skF_4')
      | v2_funct_1('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_38,c_278])).

tff(c_288,plain,(
    ! [C_35] :
      ( C_35 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',C_35) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | ~ r2_hidden(C_35,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_287])).

tff(c_853,plain,(
    ! [C_35] :
      ( C_35 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',C_35) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden(C_35,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_843,c_288])).

tff(c_856,plain,
    ( '#skF_2'('#skF_5') = '#skF_3'('#skF_5')
    | ~ r2_hidden('#skF_3'('#skF_5'),'#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_853])).

tff(c_857,plain,(
    ~ r2_hidden('#skF_3'('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_856])).

tff(c_1321,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4')
    | v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1316,c_857])).

tff(c_1330,plain,(
    v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_38,c_264,c_1321])).

tff(c_1332,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1330])).

tff(c_1334,plain,(
    v2_funct_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_46,plain,
    ( r2_hidden('#skF_6','#skF_4')
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1336,plain,(
    r2_hidden('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1334,c_46])).

tff(c_1833,plain,(
    ! [D_246,C_247,B_248,A_249] :
      ( k1_funct_1(k2_funct_1(D_246),k1_funct_1(D_246,C_247)) = C_247
      | k1_xboole_0 = B_248
      | ~ r2_hidden(C_247,A_249)
      | ~ v2_funct_1(D_246)
      | ~ m1_subset_1(D_246,k1_zfmisc_1(k2_zfmisc_1(A_249,B_248)))
      | ~ v1_funct_2(D_246,A_249,B_248)
      | ~ v1_funct_1(D_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1880,plain,(
    ! [D_252,B_253] :
      ( k1_funct_1(k2_funct_1(D_252),k1_funct_1(D_252,'#skF_6')) = '#skF_6'
      | k1_xboole_0 = B_253
      | ~ v2_funct_1(D_252)
      | ~ m1_subset_1(D_252,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_253)))
      | ~ v1_funct_2(D_252,'#skF_4',B_253)
      | ~ v1_funct_1(D_252) ) ),
    inference(resolution,[status(thm)],[c_1336,c_1833])).

tff(c_1894,plain,
    ( k1_funct_1(k2_funct_1('#skF_5'),k1_funct_1('#skF_5','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_4'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_2('#skF_5','#skF_4','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_1880])).

tff(c_1901,plain,
    ( k1_funct_1(k2_funct_1('#skF_5'),k1_funct_1('#skF_5','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_1334,c_1894])).

tff(c_1902,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1901])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_44,plain,
    ( r2_hidden('#skF_7','#skF_4')
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1338,plain,(
    r2_hidden('#skF_7','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1334,c_44])).

tff(c_1396,plain,(
    ! [C_190,B_191,A_192] :
      ( r2_hidden(C_190,B_191)
      | ~ r2_hidden(C_190,A_192)
      | ~ r1_tarski(A_192,B_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1413,plain,(
    ! [B_196] :
      ( r2_hidden('#skF_7',B_196)
      | ~ r1_tarski('#skF_4',B_196) ) ),
    inference(resolution,[status(thm)],[c_1338,c_1396])).

tff(c_24,plain,(
    ! [B_17,A_16] :
      ( ~ r1_tarski(B_17,A_16)
      | ~ r2_hidden(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1429,plain,(
    ! [B_198] :
      ( ~ r1_tarski(B_198,'#skF_7')
      | ~ r1_tarski('#skF_4',B_198) ) ),
    inference(resolution,[status(thm)],[c_1413,c_24])).

tff(c_1437,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_1429])).

tff(c_1920,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1902,c_1437])).

tff(c_1925,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1395,c_1920])).

tff(c_1927,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1901])).

tff(c_1333,plain,(
    '#skF_7' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_1926,plain,(
    k1_funct_1(k2_funct_1('#skF_5'),k1_funct_1('#skF_5','#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1901])).

tff(c_42,plain,
    ( k1_funct_1('#skF_5','#skF_7') = k1_funct_1('#skF_5','#skF_6')
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1369,plain,(
    k1_funct_1('#skF_5','#skF_7') = k1_funct_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1334,c_42])).

tff(c_2052,plain,(
    ! [D_262,B_263] :
      ( k1_funct_1(k2_funct_1(D_262),k1_funct_1(D_262,'#skF_7')) = '#skF_7'
      | k1_xboole_0 = B_263
      | ~ v2_funct_1(D_262)
      | ~ m1_subset_1(D_262,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_263)))
      | ~ v1_funct_2(D_262,'#skF_4',B_263)
      | ~ v1_funct_1(D_262) ) ),
    inference(resolution,[status(thm)],[c_1338,c_1833])).

tff(c_2066,plain,
    ( k1_funct_1(k2_funct_1('#skF_5'),k1_funct_1('#skF_5','#skF_7')) = '#skF_7'
    | k1_xboole_0 = '#skF_4'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_2('#skF_5','#skF_4','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_2052])).

tff(c_2073,plain,
    ( '#skF_7' = '#skF_6'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_1334,c_1926,c_1369,c_2066])).

tff(c_2075,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1927,c_1333,c_2073])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:12:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.80/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.94/1.65  
% 3.94/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.94/1.65  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 3.94/1.65  
% 3.94/1.65  %Foreground sorts:
% 3.94/1.65  
% 3.94/1.65  
% 3.94/1.65  %Background operators:
% 3.94/1.65  
% 3.94/1.65  
% 3.94/1.65  %Foreground operators:
% 3.94/1.65  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.94/1.65  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.94/1.65  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.94/1.65  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.94/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.94/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.94/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.94/1.65  tff('#skF_7', type, '#skF_7': $i).
% 3.94/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.94/1.65  tff('#skF_5', type, '#skF_5': $i).
% 3.94/1.65  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.94/1.65  tff('#skF_6', type, '#skF_6': $i).
% 3.94/1.65  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.94/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.94/1.65  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.94/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.94/1.65  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.94/1.65  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.94/1.65  tff('#skF_4', type, '#skF_4': $i).
% 3.94/1.65  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.94/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.94/1.65  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.94/1.65  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.94/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.94/1.65  
% 3.94/1.67  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.94/1.67  tff(f_102, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) <=> (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_funct_2)).
% 3.94/1.67  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.94/1.67  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.94/1.67  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 3.94/1.67  tff(f_38, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.94/1.67  tff(f_53, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_funct_1)).
% 3.94/1.67  tff(f_84, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(D) & r2_hidden(C, A)) => ((B = k1_xboole_0) | (k1_funct_1(k2_funct_1(D), k1_funct_1(D, C)) = C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_funct_2)).
% 3.94/1.67  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.94/1.67  tff(f_58, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.94/1.67  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.94/1.67  tff(c_1390, plain, (![A_188, B_189]: (~r2_hidden('#skF_1'(A_188, B_189), B_189) | r1_tarski(A_188, B_189))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.94/1.67  tff(c_1395, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_1390])).
% 3.94/1.67  tff(c_38, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.94/1.67  tff(c_36, plain, (v1_funct_2('#skF_5', '#skF_4', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.94/1.67  tff(c_40, plain, ('#skF_7'!='#skF_6' | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.94/1.67  tff(c_60, plain, (~v2_funct_1('#skF_5')), inference(splitLeft, [status(thm)], [c_40])).
% 3.94/1.67  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.94/1.67  tff(c_83, plain, (![C_48, A_49, B_50]: (v1_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.94/1.67  tff(c_92, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_83])).
% 3.94/1.67  tff(c_189, plain, (![A_77, B_78, C_79]: (k1_relset_1(A_77, B_78, C_79)=k1_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.94/1.67  tff(c_198, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_189])).
% 3.94/1.67  tff(c_235, plain, (![A_87, B_88, C_89]: (m1_subset_1(k1_relset_1(A_87, B_88, C_89), k1_zfmisc_1(A_87)) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.94/1.67  tff(c_255, plain, (m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_198, c_235])).
% 3.94/1.67  tff(c_260, plain, (m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_255])).
% 3.94/1.67  tff(c_10, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.94/1.67  tff(c_264, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_260, c_10])).
% 3.94/1.67  tff(c_130, plain, (![A_63]: (r2_hidden('#skF_3'(A_63), k1_relat_1(A_63)) | v2_funct_1(A_63) | ~v1_funct_1(A_63) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.94/1.67  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.94/1.67  tff(c_1316, plain, (![A_172, B_173]: (r2_hidden('#skF_3'(A_172), B_173) | ~r1_tarski(k1_relat_1(A_172), B_173) | v2_funct_1(A_172) | ~v1_funct_1(A_172) | ~v1_relat_1(A_172))), inference(resolution, [status(thm)], [c_130, c_2])).
% 3.94/1.67  tff(c_123, plain, (![A_62]: ('#skF_2'(A_62)!='#skF_3'(A_62) | v2_funct_1(A_62) | ~v1_funct_1(A_62) | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.94/1.67  tff(c_126, plain, ('#skF_2'('#skF_5')!='#skF_3'('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_123, c_60])).
% 3.94/1.67  tff(c_129, plain, ('#skF_2'('#skF_5')!='#skF_3'('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_38, c_126])).
% 3.94/1.67  tff(c_138, plain, (![A_64]: (r2_hidden('#skF_2'(A_64), k1_relat_1(A_64)) | v2_funct_1(A_64) | ~v1_funct_1(A_64) | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.94/1.67  tff(c_825, plain, (![A_132, B_133]: (r2_hidden('#skF_2'(A_132), B_133) | ~r1_tarski(k1_relat_1(A_132), B_133) | v2_funct_1(A_132) | ~v1_funct_1(A_132) | ~v1_relat_1(A_132))), inference(resolution, [status(thm)], [c_138, c_2])).
% 3.94/1.67  tff(c_272, plain, (![A_92]: (k1_funct_1(A_92, '#skF_2'(A_92))=k1_funct_1(A_92, '#skF_3'(A_92)) | v2_funct_1(A_92) | ~v1_funct_1(A_92) | ~v1_relat_1(A_92))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.94/1.67  tff(c_58, plain, (![D_36, C_35]: (v2_funct_1('#skF_5') | D_36=C_35 | k1_funct_1('#skF_5', D_36)!=k1_funct_1('#skF_5', C_35) | ~r2_hidden(D_36, '#skF_4') | ~r2_hidden(C_35, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.94/1.67  tff(c_146, plain, (![D_36, C_35]: (D_36=C_35 | k1_funct_1('#skF_5', D_36)!=k1_funct_1('#skF_5', C_35) | ~r2_hidden(D_36, '#skF_4') | ~r2_hidden(C_35, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_60, c_58])).
% 3.94/1.67  tff(c_281, plain, (![D_36]: (D_36='#skF_2'('#skF_5') | k1_funct_1('#skF_5', D_36)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden(D_36, '#skF_4') | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4') | v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_272, c_146])).
% 3.94/1.67  tff(c_290, plain, (![D_36]: (D_36='#skF_2'('#skF_5') | k1_funct_1('#skF_5', D_36)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden(D_36, '#skF_4') | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4') | v2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_38, c_281])).
% 3.94/1.67  tff(c_291, plain, (![D_36]: (D_36='#skF_2'('#skF_5') | k1_funct_1('#skF_5', D_36)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden(D_36, '#skF_4') | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_60, c_290])).
% 3.94/1.67  tff(c_442, plain, (~r2_hidden('#skF_2'('#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_291])).
% 3.94/1.67  tff(c_830, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_4') | v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_825, c_442])).
% 3.94/1.67  tff(c_839, plain, (v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_38, c_264, c_830])).
% 3.94/1.67  tff(c_841, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_839])).
% 3.94/1.67  tff(c_843, plain, (r2_hidden('#skF_2'('#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_291])).
% 3.94/1.67  tff(c_278, plain, (![C_35]: (C_35='#skF_2'('#skF_5') | k1_funct_1('#skF_5', C_35)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4') | ~r2_hidden(C_35, '#skF_4') | v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_272, c_146])).
% 3.94/1.67  tff(c_287, plain, (![C_35]: (C_35='#skF_2'('#skF_5') | k1_funct_1('#skF_5', C_35)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4') | ~r2_hidden(C_35, '#skF_4') | v2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_38, c_278])).
% 3.94/1.67  tff(c_288, plain, (![C_35]: (C_35='#skF_2'('#skF_5') | k1_funct_1('#skF_5', C_35)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4') | ~r2_hidden(C_35, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_60, c_287])).
% 3.94/1.67  tff(c_853, plain, (![C_35]: (C_35='#skF_2'('#skF_5') | k1_funct_1('#skF_5', C_35)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden(C_35, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_843, c_288])).
% 3.94/1.67  tff(c_856, plain, ('#skF_2'('#skF_5')='#skF_3'('#skF_5') | ~r2_hidden('#skF_3'('#skF_5'), '#skF_4')), inference(reflexivity, [status(thm), theory('equality')], [c_853])).
% 3.94/1.67  tff(c_857, plain, (~r2_hidden('#skF_3'('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_129, c_856])).
% 3.94/1.67  tff(c_1321, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_4') | v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1316, c_857])).
% 3.94/1.67  tff(c_1330, plain, (v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_38, c_264, c_1321])).
% 3.94/1.67  tff(c_1332, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_1330])).
% 3.94/1.67  tff(c_1334, plain, (v2_funct_1('#skF_5')), inference(splitRight, [status(thm)], [c_40])).
% 3.94/1.67  tff(c_46, plain, (r2_hidden('#skF_6', '#skF_4') | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.94/1.67  tff(c_1336, plain, (r2_hidden('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1334, c_46])).
% 3.94/1.67  tff(c_1833, plain, (![D_246, C_247, B_248, A_249]: (k1_funct_1(k2_funct_1(D_246), k1_funct_1(D_246, C_247))=C_247 | k1_xboole_0=B_248 | ~r2_hidden(C_247, A_249) | ~v2_funct_1(D_246) | ~m1_subset_1(D_246, k1_zfmisc_1(k2_zfmisc_1(A_249, B_248))) | ~v1_funct_2(D_246, A_249, B_248) | ~v1_funct_1(D_246))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.94/1.67  tff(c_1880, plain, (![D_252, B_253]: (k1_funct_1(k2_funct_1(D_252), k1_funct_1(D_252, '#skF_6'))='#skF_6' | k1_xboole_0=B_253 | ~v2_funct_1(D_252) | ~m1_subset_1(D_252, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_253))) | ~v1_funct_2(D_252, '#skF_4', B_253) | ~v1_funct_1(D_252))), inference(resolution, [status(thm)], [c_1336, c_1833])).
% 3.94/1.67  tff(c_1894, plain, (k1_funct_1(k2_funct_1('#skF_5'), k1_funct_1('#skF_5', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_4' | ~v2_funct_1('#skF_5') | ~v1_funct_2('#skF_5', '#skF_4', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_1880])).
% 3.94/1.67  tff(c_1901, plain, (k1_funct_1(k2_funct_1('#skF_5'), k1_funct_1('#skF_5', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_1334, c_1894])).
% 3.94/1.67  tff(c_1902, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_1901])).
% 3.94/1.67  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.94/1.67  tff(c_44, plain, (r2_hidden('#skF_7', '#skF_4') | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.94/1.67  tff(c_1338, plain, (r2_hidden('#skF_7', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1334, c_44])).
% 3.94/1.67  tff(c_1396, plain, (![C_190, B_191, A_192]: (r2_hidden(C_190, B_191) | ~r2_hidden(C_190, A_192) | ~r1_tarski(A_192, B_191))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.94/1.67  tff(c_1413, plain, (![B_196]: (r2_hidden('#skF_7', B_196) | ~r1_tarski('#skF_4', B_196))), inference(resolution, [status(thm)], [c_1338, c_1396])).
% 3.94/1.67  tff(c_24, plain, (![B_17, A_16]: (~r1_tarski(B_17, A_16) | ~r2_hidden(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.94/1.67  tff(c_1429, plain, (![B_198]: (~r1_tarski(B_198, '#skF_7') | ~r1_tarski('#skF_4', B_198))), inference(resolution, [status(thm)], [c_1413, c_24])).
% 3.94/1.67  tff(c_1437, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_1429])).
% 3.94/1.67  tff(c_1920, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1902, c_1437])).
% 3.94/1.67  tff(c_1925, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1395, c_1920])).
% 3.94/1.67  tff(c_1927, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_1901])).
% 3.94/1.67  tff(c_1333, plain, ('#skF_7'!='#skF_6'), inference(splitRight, [status(thm)], [c_40])).
% 3.94/1.67  tff(c_1926, plain, (k1_funct_1(k2_funct_1('#skF_5'), k1_funct_1('#skF_5', '#skF_6'))='#skF_6'), inference(splitRight, [status(thm)], [c_1901])).
% 3.94/1.67  tff(c_42, plain, (k1_funct_1('#skF_5', '#skF_7')=k1_funct_1('#skF_5', '#skF_6') | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.94/1.67  tff(c_1369, plain, (k1_funct_1('#skF_5', '#skF_7')=k1_funct_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1334, c_42])).
% 3.94/1.67  tff(c_2052, plain, (![D_262, B_263]: (k1_funct_1(k2_funct_1(D_262), k1_funct_1(D_262, '#skF_7'))='#skF_7' | k1_xboole_0=B_263 | ~v2_funct_1(D_262) | ~m1_subset_1(D_262, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_263))) | ~v1_funct_2(D_262, '#skF_4', B_263) | ~v1_funct_1(D_262))), inference(resolution, [status(thm)], [c_1338, c_1833])).
% 3.94/1.67  tff(c_2066, plain, (k1_funct_1(k2_funct_1('#skF_5'), k1_funct_1('#skF_5', '#skF_7'))='#skF_7' | k1_xboole_0='#skF_4' | ~v2_funct_1('#skF_5') | ~v1_funct_2('#skF_5', '#skF_4', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_2052])).
% 3.94/1.67  tff(c_2073, plain, ('#skF_7'='#skF_6' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_1334, c_1926, c_1369, c_2066])).
% 3.94/1.67  tff(c_2075, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1927, c_1333, c_2073])).
% 3.94/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.94/1.67  
% 3.94/1.67  Inference rules
% 3.94/1.67  ----------------------
% 3.94/1.67  #Ref     : 5
% 3.94/1.67  #Sup     : 412
% 3.94/1.67  #Fact    : 0
% 3.94/1.67  #Define  : 0
% 3.94/1.67  #Split   : 14
% 3.94/1.67  #Chain   : 0
% 3.94/1.67  #Close   : 0
% 3.94/1.67  
% 3.94/1.67  Ordering : KBO
% 3.94/1.67  
% 3.94/1.67  Simplification rules
% 3.94/1.67  ----------------------
% 3.94/1.67  #Subsume      : 45
% 3.94/1.67  #Demod        : 209
% 3.94/1.67  #Tautology    : 156
% 3.94/1.67  #SimpNegUnit  : 8
% 3.94/1.67  #BackRed      : 20
% 3.94/1.67  
% 3.94/1.67  #Partial instantiations: 0
% 3.94/1.67  #Strategies tried      : 1
% 3.94/1.67  
% 3.94/1.67  Timing (in seconds)
% 3.94/1.67  ----------------------
% 3.94/1.67  Preprocessing        : 0.33
% 3.94/1.67  Parsing              : 0.18
% 3.94/1.67  CNF conversion       : 0.02
% 3.94/1.67  Main loop            : 0.56
% 3.94/1.67  Inferencing          : 0.20
% 3.94/1.67  Reduction            : 0.18
% 3.94/1.67  Demodulation         : 0.13
% 3.94/1.67  BG Simplification    : 0.03
% 3.94/1.67  Subsumption          : 0.10
% 3.94/1.67  Abstraction          : 0.03
% 3.94/1.67  MUC search           : 0.00
% 3.94/1.67  Cooper               : 0.00
% 3.94/1.67  Total                : 0.93
% 3.94/1.67  Index Insertion      : 0.00
% 3.94/1.67  Index Deletion       : 0.00
% 3.94/1.67  Index Matching       : 0.00
% 3.94/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
