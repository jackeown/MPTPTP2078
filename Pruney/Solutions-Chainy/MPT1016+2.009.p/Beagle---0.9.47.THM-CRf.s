%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:41 EST 2020

% Result     : Theorem 3.95s
% Output     : CNFRefutation 3.95s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 414 expanded)
%              Number of leaves         :   34 ( 151 expanded)
%              Depth                    :   13
%              Number of atoms          :  263 (1325 expanded)
%              Number of equality atoms :   69 ( 318 expanded)
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

tff(f_103,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_funct_2)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
      <=> ! [B,C] :
            ( ( r2_hidden(B,k1_relat_1(A))
              & r2_hidden(C,k1_relat_1(A))
              & k1_funct_1(A,B) = k1_funct_1(A,C) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_85,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(D)
          & r2_hidden(C,A) )
       => ( B = k1_xboole_0
          | k1_funct_1(k2_funct_1(D),k1_funct_1(D,C)) = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_44,plain,
    ( '#skF_7' != '#skF_6'
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_66,plain,(
    ~ v2_funct_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_77,plain,(
    ! [C_43,A_44,B_45] :
      ( v1_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_86,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_77])).

tff(c_42,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_173,plain,(
    ! [A_69,B_70,C_71] :
      ( k1_relset_1(A_69,B_70,C_71) = k1_relat_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_182,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_173])).

tff(c_203,plain,(
    ! [A_75,B_76,C_77] :
      ( m1_subset_1(k1_relset_1(A_75,B_76,C_77),k1_zfmisc_1(A_75))
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_217,plain,
    ( m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_203])).

tff(c_222,plain,(
    m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_217])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | ~ m1_subset_1(A_9,k1_zfmisc_1(B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_226,plain,(
    r1_tarski(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_222,c_16])).

tff(c_156,plain,(
    ! [A_64] :
      ( r2_hidden('#skF_3'(A_64),k1_relat_1(A_64))
      | v2_funct_1(A_64)
      | ~ v1_funct_1(A_64)
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_836,plain,(
    ! [A_152,B_153] :
      ( r2_hidden('#skF_3'(A_152),B_153)
      | ~ r1_tarski(k1_relat_1(A_152),B_153)
      | v2_funct_1(A_152)
      | ~ v1_funct_1(A_152)
      | ~ v1_relat_1(A_152) ) ),
    inference(resolution,[status(thm)],[c_156,c_2])).

tff(c_149,plain,(
    ! [A_63] :
      ( '#skF_2'(A_63) != '#skF_3'(A_63)
      | v2_funct_1(A_63)
      | ~ v1_funct_1(A_63)
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_152,plain,
    ( '#skF_2'('#skF_5') != '#skF_3'('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_149,c_66])).

tff(c_155,plain,(
    '#skF_2'('#skF_5') != '#skF_3'('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_42,c_152])).

tff(c_160,plain,(
    ! [A_65] :
      ( r2_hidden('#skF_2'(A_65),k1_relat_1(A_65))
      | v2_funct_1(A_65)
      | ~ v1_funct_1(A_65)
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_554,plain,(
    ! [A_114,B_115] :
      ( r2_hidden('#skF_2'(A_114),B_115)
      | ~ r1_tarski(k1_relat_1(A_114),B_115)
      | v2_funct_1(A_114)
      | ~ v1_funct_1(A_114)
      | ~ v1_relat_1(A_114) ) ),
    inference(resolution,[status(thm)],[c_160,c_2])).

tff(c_276,plain,(
    ! [A_85] :
      ( k1_funct_1(A_85,'#skF_2'(A_85)) = k1_funct_1(A_85,'#skF_3'(A_85))
      | v2_funct_1(A_85)
      | ~ v1_funct_1(A_85)
      | ~ v1_relat_1(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_62,plain,(
    ! [D_36,C_35] :
      ( v2_funct_1('#skF_5')
      | D_36 = C_35
      | k1_funct_1('#skF_5',D_36) != k1_funct_1('#skF_5',C_35)
      | ~ r2_hidden(D_36,'#skF_4')
      | ~ r2_hidden(C_35,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_105,plain,(
    ! [D_36,C_35] :
      ( D_36 = C_35
      | k1_funct_1('#skF_5',D_36) != k1_funct_1('#skF_5',C_35)
      | ~ r2_hidden(D_36,'#skF_4')
      | ~ r2_hidden(C_35,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_62])).

tff(c_282,plain,(
    ! [C_35] :
      ( C_35 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',C_35) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | ~ r2_hidden(C_35,'#skF_4')
      | v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_276,c_105])).

tff(c_291,plain,(
    ! [C_35] :
      ( C_35 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',C_35) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | ~ r2_hidden(C_35,'#skF_4')
      | v2_funct_1('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_42,c_282])).

tff(c_292,plain,(
    ! [C_35] :
      ( C_35 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',C_35) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | ~ r2_hidden(C_35,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_291])).

tff(c_372,plain,(
    ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_292])).

tff(c_557,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4')
    | v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_554,c_372])).

tff(c_562,plain,(
    v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_42,c_226,c_557])).

tff(c_564,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_562])).

tff(c_566,plain,(
    r2_hidden('#skF_2'('#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_292])).

tff(c_285,plain,(
    ! [D_36] :
      ( D_36 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',D_36) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden(D_36,'#skF_4')
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_276,c_105])).

tff(c_294,plain,(
    ! [D_36] :
      ( D_36 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',D_36) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden(D_36,'#skF_4')
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | v2_funct_1('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_42,c_285])).

tff(c_295,plain,(
    ! [D_36] :
      ( D_36 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',D_36) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden(D_36,'#skF_4')
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_294])).

tff(c_584,plain,(
    ! [D_36] :
      ( D_36 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',D_36) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden(D_36,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_566,c_295])).

tff(c_587,plain,
    ( '#skF_2'('#skF_5') = '#skF_3'('#skF_5')
    | ~ r2_hidden('#skF_3'('#skF_5'),'#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_584])).

tff(c_588,plain,(
    ~ r2_hidden('#skF_3'('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_155,c_587])).

tff(c_841,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4')
    | v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_836,c_588])).

tff(c_847,plain,(
    v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_42,c_226,c_841])).

tff(c_849,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_847])).

tff(c_850,plain,(
    '#skF_7' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_40,plain,(
    v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_851,plain,(
    v2_funct_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_46,plain,
    ( k1_funct_1('#skF_5','#skF_7') = k1_funct_1('#skF_5','#skF_6')
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_862,plain,(
    k1_funct_1('#skF_5','#skF_7') = k1_funct_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_851,c_46])).

tff(c_48,plain,
    ( r2_hidden('#skF_7','#skF_4')
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_855,plain,(
    r2_hidden('#skF_7','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_851,c_48])).

tff(c_1326,plain,(
    ! [D_224,C_225,B_226,A_227] :
      ( k1_funct_1(k2_funct_1(D_224),k1_funct_1(D_224,C_225)) = C_225
      | k1_xboole_0 = B_226
      | ~ r2_hidden(C_225,A_227)
      | ~ v2_funct_1(D_224)
      | ~ m1_subset_1(D_224,k1_zfmisc_1(k2_zfmisc_1(A_227,B_226)))
      | ~ v1_funct_2(D_224,A_227,B_226)
      | ~ v1_funct_1(D_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1381,plain,(
    ! [D_234,B_235] :
      ( k1_funct_1(k2_funct_1(D_234),k1_funct_1(D_234,'#skF_7')) = '#skF_7'
      | k1_xboole_0 = B_235
      | ~ v2_funct_1(D_234)
      | ~ m1_subset_1(D_234,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_235)))
      | ~ v1_funct_2(D_234,'#skF_4',B_235)
      | ~ v1_funct_1(D_234) ) ),
    inference(resolution,[status(thm)],[c_855,c_1326])).

tff(c_1392,plain,
    ( k1_funct_1(k2_funct_1('#skF_5'),k1_funct_1('#skF_5','#skF_7')) = '#skF_7'
    | k1_xboole_0 = '#skF_4'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_2('#skF_5','#skF_4','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_1381])).

tff(c_1398,plain,
    ( k1_funct_1(k2_funct_1('#skF_5'),k1_funct_1('#skF_5','#skF_6')) = '#skF_7'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_851,c_862,c_1392])).

tff(c_1424,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1398])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_934,plain,(
    ! [C_173,B_174,A_175] :
      ( r2_hidden(C_173,B_174)
      | ~ r2_hidden(C_173,A_175)
      | ~ r1_tarski(A_175,B_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_944,plain,(
    ! [B_176] :
      ( r2_hidden('#skF_7',B_176)
      | ~ r1_tarski('#skF_4',B_176) ) ),
    inference(resolution,[status(thm)],[c_855,c_934])).

tff(c_952,plain,(
    ! [B_178,B_179] :
      ( r2_hidden('#skF_7',B_178)
      | ~ r1_tarski(B_179,B_178)
      | ~ r1_tarski('#skF_4',B_179) ) ),
    inference(resolution,[status(thm)],[c_944,c_2])).

tff(c_961,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_7',A_8)
      | ~ r1_tarski('#skF_4',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_952])).

tff(c_963,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_961])).

tff(c_1434,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1424,c_963])).

tff(c_1440,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1434])).

tff(c_1442,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1398])).

tff(c_1441,plain,(
    k1_funct_1(k2_funct_1('#skF_5'),k1_funct_1('#skF_5','#skF_6')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_1398])).

tff(c_50,plain,
    ( r2_hidden('#skF_6','#skF_4')
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_853,plain,(
    r2_hidden('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_851,c_50])).

tff(c_1493,plain,(
    ! [D_245,B_246] :
      ( k1_funct_1(k2_funct_1(D_245),k1_funct_1(D_245,'#skF_6')) = '#skF_6'
      | k1_xboole_0 = B_246
      | ~ v2_funct_1(D_245)
      | ~ m1_subset_1(D_245,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_246)))
      | ~ v1_funct_2(D_245,'#skF_4',B_246)
      | ~ v1_funct_1(D_245) ) ),
    inference(resolution,[status(thm)],[c_853,c_1326])).

tff(c_1504,plain,
    ( k1_funct_1(k2_funct_1('#skF_5'),k1_funct_1('#skF_5','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_4'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_2('#skF_5','#skF_4','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_1493])).

tff(c_1510,plain,
    ( '#skF_7' = '#skF_6'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_851,c_1441,c_1504])).

tff(c_1512,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1442,c_850,c_1510])).

tff(c_1514,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_961])).

tff(c_898,plain,(
    ! [B_164,A_165] :
      ( B_164 = A_165
      | ~ r1_tarski(B_164,A_165)
      | ~ r1_tarski(A_165,B_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_910,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_898])).

tff(c_1528,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1514,c_910])).

tff(c_1535,plain,(
    ! [A_8] : r1_tarski('#skF_4',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1528,c_14])).

tff(c_943,plain,(
    ! [B_174] :
      ( r2_hidden('#skF_6',B_174)
      | ~ r1_tarski('#skF_4',B_174) ) ),
    inference(resolution,[status(thm)],[c_853,c_934])).

tff(c_1547,plain,(
    ! [B_174] : r2_hidden('#skF_6',B_174) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1535,c_943])).

tff(c_872,plain,(
    ! [C_158,A_159,B_160] :
      ( v1_relat_1(C_158)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(A_159,B_160))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_881,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_872])).

tff(c_1595,plain,(
    ! [A_256,B_257,C_258] :
      ( k1_relset_1(A_256,B_257,C_258) = k1_relat_1(C_258)
      | ~ m1_subset_1(C_258,k1_zfmisc_1(k2_zfmisc_1(A_256,B_257))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1604,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_1595])).

tff(c_1642,plain,(
    ! [A_266,B_267,C_268] :
      ( m1_subset_1(k1_relset_1(A_266,B_267,C_268),k1_zfmisc_1(A_266))
      | ~ m1_subset_1(C_268,k1_zfmisc_1(k2_zfmisc_1(A_266,B_267))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1662,plain,
    ( m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1604,c_1642])).

tff(c_1667,plain,(
    m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1662])).

tff(c_1671,plain,(
    r1_tarski(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_1667,c_16])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1685,plain,
    ( k1_relat_1('#skF_5') = '#skF_4'
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_1671,c_8])).

tff(c_1689,plain,(
    k1_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1535,c_1685])).

tff(c_1513,plain,(
    ! [A_8] : r2_hidden('#skF_7',A_8) ),
    inference(splitRight,[status(thm)],[c_961])).

tff(c_1811,plain,(
    ! [C_275,B_276,A_277] :
      ( C_275 = B_276
      | k1_funct_1(A_277,C_275) != k1_funct_1(A_277,B_276)
      | ~ r2_hidden(C_275,k1_relat_1(A_277))
      | ~ r2_hidden(B_276,k1_relat_1(A_277))
      | ~ v2_funct_1(A_277)
      | ~ v1_funct_1(A_277)
      | ~ v1_relat_1(A_277) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1817,plain,(
    ! [B_276] :
      ( B_276 = '#skF_7'
      | k1_funct_1('#skF_5',B_276) != k1_funct_1('#skF_5','#skF_6')
      | ~ r2_hidden('#skF_7',k1_relat_1('#skF_5'))
      | ~ r2_hidden(B_276,k1_relat_1('#skF_5'))
      | ~ v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_862,c_1811])).

tff(c_1861,plain,(
    ! [B_284] :
      ( B_284 = '#skF_7'
      | k1_funct_1('#skF_5',B_284) != k1_funct_1('#skF_5','#skF_6')
      | ~ r2_hidden(B_284,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_881,c_42,c_851,c_1689,c_1513,c_1817])).

tff(c_1869,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1547,c_1861])).

tff(c_1882,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_850,c_1869])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:05:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.95/1.70  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.95/1.72  
% 3.95/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.95/1.72  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 3.95/1.72  
% 3.95/1.72  %Foreground sorts:
% 3.95/1.72  
% 3.95/1.72  
% 3.95/1.72  %Background operators:
% 3.95/1.72  
% 3.95/1.72  
% 3.95/1.72  %Foreground operators:
% 3.95/1.72  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.95/1.72  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.95/1.72  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.95/1.72  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.95/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.95/1.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.95/1.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.95/1.72  tff('#skF_7', type, '#skF_7': $i).
% 3.95/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.95/1.72  tff('#skF_5', type, '#skF_5': $i).
% 3.95/1.72  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.95/1.72  tff('#skF_6', type, '#skF_6': $i).
% 3.95/1.72  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.95/1.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.95/1.72  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.95/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.95/1.72  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.95/1.72  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.95/1.72  tff('#skF_4', type, '#skF_4': $i).
% 3.95/1.72  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.95/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.95/1.72  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.95/1.72  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.95/1.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.95/1.72  
% 3.95/1.74  tff(f_103, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) <=> (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_funct_2)).
% 3.95/1.74  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.95/1.74  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.95/1.74  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 3.95/1.74  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.95/1.74  tff(f_59, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_funct_1)).
% 3.95/1.74  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.95/1.74  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.95/1.74  tff(f_85, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(D) & r2_hidden(C, A)) => ((B = k1_xboole_0) | (k1_funct_1(k2_funct_1(D), k1_funct_1(D, C)) = C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_funct_2)).
% 3.95/1.74  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.95/1.74  tff(c_44, plain, ('#skF_7'!='#skF_6' | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.95/1.74  tff(c_66, plain, (~v2_funct_1('#skF_5')), inference(splitLeft, [status(thm)], [c_44])).
% 3.95/1.74  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.95/1.74  tff(c_77, plain, (![C_43, A_44, B_45]: (v1_relat_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.95/1.74  tff(c_86, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_77])).
% 3.95/1.74  tff(c_42, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.95/1.74  tff(c_173, plain, (![A_69, B_70, C_71]: (k1_relset_1(A_69, B_70, C_71)=k1_relat_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.95/1.74  tff(c_182, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_173])).
% 3.95/1.74  tff(c_203, plain, (![A_75, B_76, C_77]: (m1_subset_1(k1_relset_1(A_75, B_76, C_77), k1_zfmisc_1(A_75)) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.95/1.74  tff(c_217, plain, (m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_182, c_203])).
% 3.95/1.74  tff(c_222, plain, (m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_217])).
% 3.95/1.74  tff(c_16, plain, (![A_9, B_10]: (r1_tarski(A_9, B_10) | ~m1_subset_1(A_9, k1_zfmisc_1(B_10)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.95/1.74  tff(c_226, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_222, c_16])).
% 3.95/1.74  tff(c_156, plain, (![A_64]: (r2_hidden('#skF_3'(A_64), k1_relat_1(A_64)) | v2_funct_1(A_64) | ~v1_funct_1(A_64) | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.95/1.74  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.95/1.74  tff(c_836, plain, (![A_152, B_153]: (r2_hidden('#skF_3'(A_152), B_153) | ~r1_tarski(k1_relat_1(A_152), B_153) | v2_funct_1(A_152) | ~v1_funct_1(A_152) | ~v1_relat_1(A_152))), inference(resolution, [status(thm)], [c_156, c_2])).
% 3.95/1.74  tff(c_149, plain, (![A_63]: ('#skF_2'(A_63)!='#skF_3'(A_63) | v2_funct_1(A_63) | ~v1_funct_1(A_63) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.95/1.74  tff(c_152, plain, ('#skF_2'('#skF_5')!='#skF_3'('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_149, c_66])).
% 3.95/1.74  tff(c_155, plain, ('#skF_2'('#skF_5')!='#skF_3'('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_42, c_152])).
% 3.95/1.74  tff(c_160, plain, (![A_65]: (r2_hidden('#skF_2'(A_65), k1_relat_1(A_65)) | v2_funct_1(A_65) | ~v1_funct_1(A_65) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.95/1.74  tff(c_554, plain, (![A_114, B_115]: (r2_hidden('#skF_2'(A_114), B_115) | ~r1_tarski(k1_relat_1(A_114), B_115) | v2_funct_1(A_114) | ~v1_funct_1(A_114) | ~v1_relat_1(A_114))), inference(resolution, [status(thm)], [c_160, c_2])).
% 3.95/1.74  tff(c_276, plain, (![A_85]: (k1_funct_1(A_85, '#skF_2'(A_85))=k1_funct_1(A_85, '#skF_3'(A_85)) | v2_funct_1(A_85) | ~v1_funct_1(A_85) | ~v1_relat_1(A_85))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.95/1.74  tff(c_62, plain, (![D_36, C_35]: (v2_funct_1('#skF_5') | D_36=C_35 | k1_funct_1('#skF_5', D_36)!=k1_funct_1('#skF_5', C_35) | ~r2_hidden(D_36, '#skF_4') | ~r2_hidden(C_35, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.95/1.74  tff(c_105, plain, (![D_36, C_35]: (D_36=C_35 | k1_funct_1('#skF_5', D_36)!=k1_funct_1('#skF_5', C_35) | ~r2_hidden(D_36, '#skF_4') | ~r2_hidden(C_35, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_66, c_62])).
% 3.95/1.74  tff(c_282, plain, (![C_35]: (C_35='#skF_2'('#skF_5') | k1_funct_1('#skF_5', C_35)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4') | ~r2_hidden(C_35, '#skF_4') | v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_276, c_105])).
% 3.95/1.74  tff(c_291, plain, (![C_35]: (C_35='#skF_2'('#skF_5') | k1_funct_1('#skF_5', C_35)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4') | ~r2_hidden(C_35, '#skF_4') | v2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_42, c_282])).
% 3.95/1.74  tff(c_292, plain, (![C_35]: (C_35='#skF_2'('#skF_5') | k1_funct_1('#skF_5', C_35)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4') | ~r2_hidden(C_35, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_66, c_291])).
% 3.95/1.74  tff(c_372, plain, (~r2_hidden('#skF_2'('#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_292])).
% 3.95/1.74  tff(c_557, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_4') | v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_554, c_372])).
% 3.95/1.74  tff(c_562, plain, (v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_42, c_226, c_557])).
% 3.95/1.74  tff(c_564, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_562])).
% 3.95/1.74  tff(c_566, plain, (r2_hidden('#skF_2'('#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_292])).
% 3.95/1.74  tff(c_285, plain, (![D_36]: (D_36='#skF_2'('#skF_5') | k1_funct_1('#skF_5', D_36)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden(D_36, '#skF_4') | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4') | v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_276, c_105])).
% 3.95/1.74  tff(c_294, plain, (![D_36]: (D_36='#skF_2'('#skF_5') | k1_funct_1('#skF_5', D_36)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden(D_36, '#skF_4') | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4') | v2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_42, c_285])).
% 3.95/1.74  tff(c_295, plain, (![D_36]: (D_36='#skF_2'('#skF_5') | k1_funct_1('#skF_5', D_36)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden(D_36, '#skF_4') | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_66, c_294])).
% 3.95/1.74  tff(c_584, plain, (![D_36]: (D_36='#skF_2'('#skF_5') | k1_funct_1('#skF_5', D_36)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden(D_36, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_566, c_295])).
% 3.95/1.74  tff(c_587, plain, ('#skF_2'('#skF_5')='#skF_3'('#skF_5') | ~r2_hidden('#skF_3'('#skF_5'), '#skF_4')), inference(reflexivity, [status(thm), theory('equality')], [c_584])).
% 3.95/1.74  tff(c_588, plain, (~r2_hidden('#skF_3'('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_155, c_587])).
% 3.95/1.74  tff(c_841, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_4') | v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_836, c_588])).
% 3.95/1.74  tff(c_847, plain, (v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_42, c_226, c_841])).
% 3.95/1.74  tff(c_849, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_847])).
% 3.95/1.74  tff(c_850, plain, ('#skF_7'!='#skF_6'), inference(splitRight, [status(thm)], [c_44])).
% 3.95/1.74  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.95/1.74  tff(c_40, plain, (v1_funct_2('#skF_5', '#skF_4', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.95/1.74  tff(c_851, plain, (v2_funct_1('#skF_5')), inference(splitRight, [status(thm)], [c_44])).
% 3.95/1.74  tff(c_46, plain, (k1_funct_1('#skF_5', '#skF_7')=k1_funct_1('#skF_5', '#skF_6') | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.95/1.74  tff(c_862, plain, (k1_funct_1('#skF_5', '#skF_7')=k1_funct_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_851, c_46])).
% 3.95/1.74  tff(c_48, plain, (r2_hidden('#skF_7', '#skF_4') | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.95/1.74  tff(c_855, plain, (r2_hidden('#skF_7', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_851, c_48])).
% 3.95/1.74  tff(c_1326, plain, (![D_224, C_225, B_226, A_227]: (k1_funct_1(k2_funct_1(D_224), k1_funct_1(D_224, C_225))=C_225 | k1_xboole_0=B_226 | ~r2_hidden(C_225, A_227) | ~v2_funct_1(D_224) | ~m1_subset_1(D_224, k1_zfmisc_1(k2_zfmisc_1(A_227, B_226))) | ~v1_funct_2(D_224, A_227, B_226) | ~v1_funct_1(D_224))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.95/1.74  tff(c_1381, plain, (![D_234, B_235]: (k1_funct_1(k2_funct_1(D_234), k1_funct_1(D_234, '#skF_7'))='#skF_7' | k1_xboole_0=B_235 | ~v2_funct_1(D_234) | ~m1_subset_1(D_234, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_235))) | ~v1_funct_2(D_234, '#skF_4', B_235) | ~v1_funct_1(D_234))), inference(resolution, [status(thm)], [c_855, c_1326])).
% 3.95/1.74  tff(c_1392, plain, (k1_funct_1(k2_funct_1('#skF_5'), k1_funct_1('#skF_5', '#skF_7'))='#skF_7' | k1_xboole_0='#skF_4' | ~v2_funct_1('#skF_5') | ~v1_funct_2('#skF_5', '#skF_4', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_1381])).
% 3.95/1.74  tff(c_1398, plain, (k1_funct_1(k2_funct_1('#skF_5'), k1_funct_1('#skF_5', '#skF_6'))='#skF_7' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_851, c_862, c_1392])).
% 3.95/1.74  tff(c_1424, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_1398])).
% 3.95/1.74  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.95/1.74  tff(c_934, plain, (![C_173, B_174, A_175]: (r2_hidden(C_173, B_174) | ~r2_hidden(C_173, A_175) | ~r1_tarski(A_175, B_174))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.95/1.74  tff(c_944, plain, (![B_176]: (r2_hidden('#skF_7', B_176) | ~r1_tarski('#skF_4', B_176))), inference(resolution, [status(thm)], [c_855, c_934])).
% 3.95/1.74  tff(c_952, plain, (![B_178, B_179]: (r2_hidden('#skF_7', B_178) | ~r1_tarski(B_179, B_178) | ~r1_tarski('#skF_4', B_179))), inference(resolution, [status(thm)], [c_944, c_2])).
% 3.95/1.74  tff(c_961, plain, (![A_8]: (r2_hidden('#skF_7', A_8) | ~r1_tarski('#skF_4', k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_952])).
% 3.95/1.74  tff(c_963, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_961])).
% 3.95/1.74  tff(c_1434, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1424, c_963])).
% 3.95/1.74  tff(c_1440, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_1434])).
% 3.95/1.74  tff(c_1442, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_1398])).
% 3.95/1.74  tff(c_1441, plain, (k1_funct_1(k2_funct_1('#skF_5'), k1_funct_1('#skF_5', '#skF_6'))='#skF_7'), inference(splitRight, [status(thm)], [c_1398])).
% 3.95/1.74  tff(c_50, plain, (r2_hidden('#skF_6', '#skF_4') | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.95/1.74  tff(c_853, plain, (r2_hidden('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_851, c_50])).
% 3.95/1.74  tff(c_1493, plain, (![D_245, B_246]: (k1_funct_1(k2_funct_1(D_245), k1_funct_1(D_245, '#skF_6'))='#skF_6' | k1_xboole_0=B_246 | ~v2_funct_1(D_245) | ~m1_subset_1(D_245, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_246))) | ~v1_funct_2(D_245, '#skF_4', B_246) | ~v1_funct_1(D_245))), inference(resolution, [status(thm)], [c_853, c_1326])).
% 3.95/1.74  tff(c_1504, plain, (k1_funct_1(k2_funct_1('#skF_5'), k1_funct_1('#skF_5', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_4' | ~v2_funct_1('#skF_5') | ~v1_funct_2('#skF_5', '#skF_4', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_1493])).
% 3.95/1.74  tff(c_1510, plain, ('#skF_7'='#skF_6' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_851, c_1441, c_1504])).
% 3.95/1.74  tff(c_1512, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1442, c_850, c_1510])).
% 3.95/1.74  tff(c_1514, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(splitRight, [status(thm)], [c_961])).
% 3.95/1.74  tff(c_898, plain, (![B_164, A_165]: (B_164=A_165 | ~r1_tarski(B_164, A_165) | ~r1_tarski(A_165, B_164))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.95/1.74  tff(c_910, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_898])).
% 3.95/1.74  tff(c_1528, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_1514, c_910])).
% 3.95/1.74  tff(c_1535, plain, (![A_8]: (r1_tarski('#skF_4', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_1528, c_14])).
% 3.95/1.74  tff(c_943, plain, (![B_174]: (r2_hidden('#skF_6', B_174) | ~r1_tarski('#skF_4', B_174))), inference(resolution, [status(thm)], [c_853, c_934])).
% 3.95/1.74  tff(c_1547, plain, (![B_174]: (r2_hidden('#skF_6', B_174))), inference(demodulation, [status(thm), theory('equality')], [c_1535, c_943])).
% 3.95/1.74  tff(c_872, plain, (![C_158, A_159, B_160]: (v1_relat_1(C_158) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(A_159, B_160))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.95/1.74  tff(c_881, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_872])).
% 3.95/1.74  tff(c_1595, plain, (![A_256, B_257, C_258]: (k1_relset_1(A_256, B_257, C_258)=k1_relat_1(C_258) | ~m1_subset_1(C_258, k1_zfmisc_1(k2_zfmisc_1(A_256, B_257))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.95/1.74  tff(c_1604, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_1595])).
% 3.95/1.74  tff(c_1642, plain, (![A_266, B_267, C_268]: (m1_subset_1(k1_relset_1(A_266, B_267, C_268), k1_zfmisc_1(A_266)) | ~m1_subset_1(C_268, k1_zfmisc_1(k2_zfmisc_1(A_266, B_267))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.95/1.74  tff(c_1662, plain, (m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_1604, c_1642])).
% 3.95/1.74  tff(c_1667, plain, (m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1662])).
% 3.95/1.74  tff(c_1671, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_1667, c_16])).
% 3.95/1.74  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.95/1.74  tff(c_1685, plain, (k1_relat_1('#skF_5')='#skF_4' | ~r1_tarski('#skF_4', k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_1671, c_8])).
% 3.95/1.74  tff(c_1689, plain, (k1_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1535, c_1685])).
% 3.95/1.74  tff(c_1513, plain, (![A_8]: (r2_hidden('#skF_7', A_8))), inference(splitRight, [status(thm)], [c_961])).
% 3.95/1.74  tff(c_1811, plain, (![C_275, B_276, A_277]: (C_275=B_276 | k1_funct_1(A_277, C_275)!=k1_funct_1(A_277, B_276) | ~r2_hidden(C_275, k1_relat_1(A_277)) | ~r2_hidden(B_276, k1_relat_1(A_277)) | ~v2_funct_1(A_277) | ~v1_funct_1(A_277) | ~v1_relat_1(A_277))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.95/1.74  tff(c_1817, plain, (![B_276]: (B_276='#skF_7' | k1_funct_1('#skF_5', B_276)!=k1_funct_1('#skF_5', '#skF_6') | ~r2_hidden('#skF_7', k1_relat_1('#skF_5')) | ~r2_hidden(B_276, k1_relat_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_862, c_1811])).
% 3.95/1.74  tff(c_1861, plain, (![B_284]: (B_284='#skF_7' | k1_funct_1('#skF_5', B_284)!=k1_funct_1('#skF_5', '#skF_6') | ~r2_hidden(B_284, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_881, c_42, c_851, c_1689, c_1513, c_1817])).
% 3.95/1.74  tff(c_1869, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_1547, c_1861])).
% 3.95/1.74  tff(c_1882, plain, $false, inference(negUnitSimplification, [status(thm)], [c_850, c_1869])).
% 3.95/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.95/1.74  
% 3.95/1.74  Inference rules
% 3.95/1.74  ----------------------
% 3.95/1.74  #Ref     : 6
% 3.95/1.74  #Sup     : 384
% 3.95/1.74  #Fact    : 0
% 3.95/1.74  #Define  : 0
% 3.95/1.74  #Split   : 16
% 3.95/1.74  #Chain   : 0
% 3.95/1.74  #Close   : 0
% 3.95/1.74  
% 3.95/1.74  Ordering : KBO
% 3.95/1.74  
% 3.95/1.74  Simplification rules
% 3.95/1.74  ----------------------
% 3.95/1.74  #Subsume      : 35
% 3.95/1.74  #Demod        : 282
% 3.95/1.74  #Tautology    : 199
% 3.95/1.74  #SimpNegUnit  : 9
% 3.95/1.74  #BackRed      : 33
% 3.95/1.74  
% 3.95/1.74  #Partial instantiations: 0
% 3.95/1.74  #Strategies tried      : 1
% 3.95/1.74  
% 3.95/1.74  Timing (in seconds)
% 3.95/1.74  ----------------------
% 3.95/1.74  Preprocessing        : 0.35
% 3.95/1.74  Parsing              : 0.18
% 3.95/1.74  CNF conversion       : 0.02
% 3.95/1.74  Main loop            : 0.58
% 3.95/1.74  Inferencing          : 0.21
% 3.95/1.74  Reduction            : 0.19
% 3.95/1.74  Demodulation         : 0.13
% 3.95/1.74  BG Simplification    : 0.03
% 3.95/1.74  Subsumption          : 0.10
% 3.95/1.74  Abstraction          : 0.03
% 3.95/1.74  MUC search           : 0.00
% 3.95/1.74  Cooper               : 0.00
% 3.95/1.74  Total                : 0.98
% 3.95/1.74  Index Insertion      : 0.00
% 3.95/1.74  Index Deletion       : 0.00
% 3.95/1.74  Index Matching       : 0.00
% 3.95/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
