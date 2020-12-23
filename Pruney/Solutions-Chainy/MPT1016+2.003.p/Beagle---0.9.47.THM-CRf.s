%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:41 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.49s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 302 expanded)
%              Number of leaves         :   36 ( 117 expanded)
%              Depth                    :   14
%              Number of atoms          :  209 (1033 expanded)
%              Number of equality atoms :   50 ( 256 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

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

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_60,axiom,(
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

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

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

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_36,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_81,plain,(
    ! [C_45,A_46,B_47] :
      ( v1_relat_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_85,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_81])).

tff(c_87,plain,(
    ! [C_50,A_51,B_52] :
      ( v4_relat_1(C_50,A_51)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_91,plain,(
    v4_relat_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_87])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k1_relat_1(B_11),A_10)
      | ~ v4_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_42,plain,
    ( '#skF_7' != '#skF_8'
    | ~ v2_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_61,plain,(
    ~ v2_funct_1('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_40,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_166,plain,(
    ! [A_73] :
      ( r2_hidden('#skF_3'(A_73),k1_relat_1(A_73))
      | v2_funct_1(A_73)
      | ~ v1_funct_1(A_73)
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_172,plain,(
    ! [A_73,B_6] :
      ( r2_hidden('#skF_3'(A_73),B_6)
      | ~ r1_tarski(k1_relat_1(A_73),B_6)
      | v2_funct_1(A_73)
      | ~ v1_funct_1(A_73)
      | ~ v1_relat_1(A_73) ) ),
    inference(resolution,[status(thm)],[c_166,c_6])).

tff(c_149,plain,(
    ! [A_70] :
      ( '#skF_4'(A_70) != '#skF_3'(A_70)
      | v2_funct_1(A_70)
      | ~ v1_funct_1(A_70)
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_152,plain,
    ( '#skF_4'('#skF_6') != '#skF_3'('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_149,c_61])).

tff(c_155,plain,(
    '#skF_4'('#skF_6') != '#skF_3'('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_40,c_152])).

tff(c_175,plain,(
    ! [A_75] :
      ( r2_hidden('#skF_4'(A_75),k1_relat_1(A_75))
      | v2_funct_1(A_75)
      | ~ v1_funct_1(A_75)
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_181,plain,(
    ! [A_75,B_6] :
      ( r2_hidden('#skF_4'(A_75),B_6)
      | ~ r1_tarski(k1_relat_1(A_75),B_6)
      | v2_funct_1(A_75)
      | ~ v1_funct_1(A_75)
      | ~ v1_relat_1(A_75) ) ),
    inference(resolution,[status(thm)],[c_175,c_6])).

tff(c_225,plain,(
    ! [A_88] :
      ( k1_funct_1(A_88,'#skF_4'(A_88)) = k1_funct_1(A_88,'#skF_3'(A_88))
      | v2_funct_1(A_88)
      | ~ v1_funct_1(A_88)
      | ~ v1_relat_1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_60,plain,(
    ! [D_34,C_33] :
      ( v2_funct_1('#skF_6')
      | D_34 = C_33
      | k1_funct_1('#skF_6',D_34) != k1_funct_1('#skF_6',C_33)
      | ~ r2_hidden(D_34,'#skF_5')
      | ~ r2_hidden(C_33,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_130,plain,(
    ! [D_34,C_33] :
      ( D_34 = C_33
      | k1_funct_1('#skF_6',D_34) != k1_funct_1('#skF_6',C_33)
      | ~ r2_hidden(D_34,'#skF_5')
      | ~ r2_hidden(C_33,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_60])).

tff(c_234,plain,(
    ! [D_34] :
      ( D_34 = '#skF_4'('#skF_6')
      | k1_funct_1('#skF_6',D_34) != k1_funct_1('#skF_6','#skF_3'('#skF_6'))
      | ~ r2_hidden(D_34,'#skF_5')
      | ~ r2_hidden('#skF_4'('#skF_6'),'#skF_5')
      | v2_funct_1('#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_130])).

tff(c_243,plain,(
    ! [D_34] :
      ( D_34 = '#skF_4'('#skF_6')
      | k1_funct_1('#skF_6',D_34) != k1_funct_1('#skF_6','#skF_3'('#skF_6'))
      | ~ r2_hidden(D_34,'#skF_5')
      | ~ r2_hidden('#skF_4'('#skF_6'),'#skF_5')
      | v2_funct_1('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_40,c_234])).

tff(c_244,plain,(
    ! [D_34] :
      ( D_34 = '#skF_4'('#skF_6')
      | k1_funct_1('#skF_6',D_34) != k1_funct_1('#skF_6','#skF_3'('#skF_6'))
      | ~ r2_hidden(D_34,'#skF_5')
      | ~ r2_hidden('#skF_4'('#skF_6'),'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_243])).

tff(c_339,plain,(
    ~ r2_hidden('#skF_4'('#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_244])).

tff(c_342,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_6'),'#skF_5')
    | v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_181,c_339])).

tff(c_345,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_6'),'#skF_5')
    | v2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_40,c_342])).

tff(c_346,plain,(
    ~ r1_tarski(k1_relat_1('#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_345])).

tff(c_349,plain,
    ( ~ v4_relat_1('#skF_6','#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_16,c_346])).

tff(c_356,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_91,c_349])).

tff(c_358,plain,(
    r2_hidden('#skF_4'('#skF_6'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_244])).

tff(c_231,plain,(
    ! [C_33] :
      ( C_33 = '#skF_4'('#skF_6')
      | k1_funct_1('#skF_6',C_33) != k1_funct_1('#skF_6','#skF_3'('#skF_6'))
      | ~ r2_hidden('#skF_4'('#skF_6'),'#skF_5')
      | ~ r2_hidden(C_33,'#skF_5')
      | v2_funct_1('#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_130])).

tff(c_240,plain,(
    ! [C_33] :
      ( C_33 = '#skF_4'('#skF_6')
      | k1_funct_1('#skF_6',C_33) != k1_funct_1('#skF_6','#skF_3'('#skF_6'))
      | ~ r2_hidden('#skF_4'('#skF_6'),'#skF_5')
      | ~ r2_hidden(C_33,'#skF_5')
      | v2_funct_1('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_40,c_231])).

tff(c_241,plain,(
    ! [C_33] :
      ( C_33 = '#skF_4'('#skF_6')
      | k1_funct_1('#skF_6',C_33) != k1_funct_1('#skF_6','#skF_3'('#skF_6'))
      | ~ r2_hidden('#skF_4'('#skF_6'),'#skF_5')
      | ~ r2_hidden(C_33,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_240])).

tff(c_359,plain,(
    ~ r2_hidden('#skF_4'('#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_241])).

tff(c_368,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_359])).

tff(c_369,plain,(
    ! [C_33] :
      ( C_33 = '#skF_4'('#skF_6')
      | k1_funct_1('#skF_6',C_33) != k1_funct_1('#skF_6','#skF_3'('#skF_6'))
      | ~ r2_hidden(C_33,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_241])).

tff(c_444,plain,
    ( '#skF_4'('#skF_6') = '#skF_3'('#skF_6')
    | ~ r2_hidden('#skF_3'('#skF_6'),'#skF_5') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_369])).

tff(c_445,plain,(
    ~ r2_hidden('#skF_3'('#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_155,c_444])).

tff(c_457,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_6'),'#skF_5')
    | v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_172,c_445])).

tff(c_460,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_6'),'#skF_5')
    | v2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_40,c_457])).

tff(c_461,plain,(
    ~ r1_tarski(k1_relat_1('#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_460])).

tff(c_464,plain,
    ( ~ v4_relat_1('#skF_6','#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_16,c_461])).

tff(c_471,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_91,c_464])).

tff(c_473,plain,(
    v2_funct_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_48,plain,
    ( r2_hidden('#skF_7','#skF_5')
    | ~ v2_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_475,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_473,c_48])).

tff(c_476,plain,(
    ! [B_121,A_122] :
      ( ~ r2_hidden(B_121,A_122)
      | ~ v1_xboole_0(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_480,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_475,c_476])).

tff(c_38,plain,(
    v1_funct_2('#skF_6','#skF_5','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_46,plain,
    ( r2_hidden('#skF_8','#skF_5')
    | ~ v2_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_482,plain,(
    r2_hidden('#skF_8','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_473,c_46])).

tff(c_836,plain,(
    ! [D_210,C_211,B_212,A_213] :
      ( k1_funct_1(k2_funct_1(D_210),k1_funct_1(D_210,C_211)) = C_211
      | k1_xboole_0 = B_212
      | ~ r2_hidden(C_211,A_213)
      | ~ v2_funct_1(D_210)
      | ~ m1_subset_1(D_210,k1_zfmisc_1(k2_zfmisc_1(A_213,B_212)))
      | ~ v1_funct_2(D_210,A_213,B_212)
      | ~ v1_funct_1(D_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_915,plain,(
    ! [D_224,B_225] :
      ( k1_funct_1(k2_funct_1(D_224),k1_funct_1(D_224,'#skF_8')) = '#skF_8'
      | k1_xboole_0 = B_225
      | ~ v2_funct_1(D_224)
      | ~ m1_subset_1(D_224,k1_zfmisc_1(k2_zfmisc_1('#skF_5',B_225)))
      | ~ v1_funct_2(D_224,'#skF_5',B_225)
      | ~ v1_funct_1(D_224) ) ),
    inference(resolution,[status(thm)],[c_482,c_836])).

tff(c_917,plain,
    ( k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6','#skF_8')) = '#skF_8'
    | k1_xboole_0 = '#skF_5'
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_2('#skF_6','#skF_5','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_915])).

tff(c_920,plain,
    ( k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6','#skF_8')) = '#skF_8'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_473,c_917])).

tff(c_921,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_920])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_924,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_921,c_12])).

tff(c_926,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_480,c_924])).

tff(c_928,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_920])).

tff(c_472,plain,(
    '#skF_7' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_927,plain,(
    k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6','#skF_8')) = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_920])).

tff(c_44,plain,
    ( k1_funct_1('#skF_6','#skF_7') = k1_funct_1('#skF_6','#skF_8')
    | ~ v2_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_511,plain,(
    k1_funct_1('#skF_6','#skF_7') = k1_funct_1('#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_473,c_44])).

tff(c_947,plain,(
    ! [D_230,B_231] :
      ( k1_funct_1(k2_funct_1(D_230),k1_funct_1(D_230,'#skF_7')) = '#skF_7'
      | k1_xboole_0 = B_231
      | ~ v2_funct_1(D_230)
      | ~ m1_subset_1(D_230,k1_zfmisc_1(k2_zfmisc_1('#skF_5',B_231)))
      | ~ v1_funct_2(D_230,'#skF_5',B_231)
      | ~ v1_funct_1(D_230) ) ),
    inference(resolution,[status(thm)],[c_475,c_836])).

tff(c_949,plain,
    ( k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6','#skF_7')) = '#skF_7'
    | k1_xboole_0 = '#skF_5'
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_2('#skF_6','#skF_5','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_947])).

tff(c_952,plain,
    ( '#skF_7' = '#skF_8'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_473,c_927,c_511,c_949])).

tff(c_954,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_928,c_472,c_952])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:40:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.49/1.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.66  
% 3.49/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.66  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2
% 3.49/1.66  
% 3.49/1.66  %Foreground sorts:
% 3.49/1.66  
% 3.49/1.66  
% 3.49/1.66  %Background operators:
% 3.49/1.66  
% 3.49/1.66  
% 3.49/1.66  %Foreground operators:
% 3.49/1.66  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.49/1.66  tff('#skF_4', type, '#skF_4': $i > $i).
% 3.49/1.66  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.49/1.66  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.49/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.49/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.49/1.66  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.49/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.49/1.66  tff('#skF_7', type, '#skF_7': $i).
% 3.49/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.49/1.66  tff('#skF_5', type, '#skF_5': $i).
% 3.49/1.66  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.49/1.66  tff('#skF_6', type, '#skF_6': $i).
% 3.49/1.66  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.49/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.49/1.66  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.49/1.66  tff('#skF_8', type, '#skF_8': $i).
% 3.49/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.49/1.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.49/1.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.49/1.66  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.49/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.49/1.66  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.49/1.66  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.49/1.66  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.49/1.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.49/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.49/1.66  
% 3.49/1.68  tff(f_102, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) <=> (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_funct_2)).
% 3.49/1.68  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.49/1.68  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.49/1.68  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.49/1.68  tff(f_60, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_funct_1)).
% 3.49/1.68  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.49/1.68  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.49/1.68  tff(f_84, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(D) & r2_hidden(C, A)) => ((B = k1_xboole_0) | (k1_funct_1(k2_funct_1(D), k1_funct_1(D, C)) = C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_funct_2)).
% 3.49/1.68  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.49/1.68  tff(c_36, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.49/1.68  tff(c_81, plain, (![C_45, A_46, B_47]: (v1_relat_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.49/1.68  tff(c_85, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_36, c_81])).
% 3.49/1.68  tff(c_87, plain, (![C_50, A_51, B_52]: (v4_relat_1(C_50, A_51) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.49/1.68  tff(c_91, plain, (v4_relat_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_36, c_87])).
% 3.49/1.68  tff(c_16, plain, (![B_11, A_10]: (r1_tarski(k1_relat_1(B_11), A_10) | ~v4_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.49/1.68  tff(c_42, plain, ('#skF_7'!='#skF_8' | ~v2_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.49/1.68  tff(c_61, plain, (~v2_funct_1('#skF_6')), inference(splitLeft, [status(thm)], [c_42])).
% 3.49/1.68  tff(c_40, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.49/1.68  tff(c_166, plain, (![A_73]: (r2_hidden('#skF_3'(A_73), k1_relat_1(A_73)) | v2_funct_1(A_73) | ~v1_funct_1(A_73) | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.49/1.68  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.49/1.68  tff(c_172, plain, (![A_73, B_6]: (r2_hidden('#skF_3'(A_73), B_6) | ~r1_tarski(k1_relat_1(A_73), B_6) | v2_funct_1(A_73) | ~v1_funct_1(A_73) | ~v1_relat_1(A_73))), inference(resolution, [status(thm)], [c_166, c_6])).
% 3.49/1.68  tff(c_149, plain, (![A_70]: ('#skF_4'(A_70)!='#skF_3'(A_70) | v2_funct_1(A_70) | ~v1_funct_1(A_70) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.49/1.68  tff(c_152, plain, ('#skF_4'('#skF_6')!='#skF_3'('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_149, c_61])).
% 3.49/1.68  tff(c_155, plain, ('#skF_4'('#skF_6')!='#skF_3'('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_40, c_152])).
% 3.49/1.68  tff(c_175, plain, (![A_75]: (r2_hidden('#skF_4'(A_75), k1_relat_1(A_75)) | v2_funct_1(A_75) | ~v1_funct_1(A_75) | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.49/1.68  tff(c_181, plain, (![A_75, B_6]: (r2_hidden('#skF_4'(A_75), B_6) | ~r1_tarski(k1_relat_1(A_75), B_6) | v2_funct_1(A_75) | ~v1_funct_1(A_75) | ~v1_relat_1(A_75))), inference(resolution, [status(thm)], [c_175, c_6])).
% 3.49/1.68  tff(c_225, plain, (![A_88]: (k1_funct_1(A_88, '#skF_4'(A_88))=k1_funct_1(A_88, '#skF_3'(A_88)) | v2_funct_1(A_88) | ~v1_funct_1(A_88) | ~v1_relat_1(A_88))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.49/1.68  tff(c_60, plain, (![D_34, C_33]: (v2_funct_1('#skF_6') | D_34=C_33 | k1_funct_1('#skF_6', D_34)!=k1_funct_1('#skF_6', C_33) | ~r2_hidden(D_34, '#skF_5') | ~r2_hidden(C_33, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.49/1.68  tff(c_130, plain, (![D_34, C_33]: (D_34=C_33 | k1_funct_1('#skF_6', D_34)!=k1_funct_1('#skF_6', C_33) | ~r2_hidden(D_34, '#skF_5') | ~r2_hidden(C_33, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_61, c_60])).
% 3.49/1.68  tff(c_234, plain, (![D_34]: (D_34='#skF_4'('#skF_6') | k1_funct_1('#skF_6', D_34)!=k1_funct_1('#skF_6', '#skF_3'('#skF_6')) | ~r2_hidden(D_34, '#skF_5') | ~r2_hidden('#skF_4'('#skF_6'), '#skF_5') | v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_225, c_130])).
% 3.49/1.68  tff(c_243, plain, (![D_34]: (D_34='#skF_4'('#skF_6') | k1_funct_1('#skF_6', D_34)!=k1_funct_1('#skF_6', '#skF_3'('#skF_6')) | ~r2_hidden(D_34, '#skF_5') | ~r2_hidden('#skF_4'('#skF_6'), '#skF_5') | v2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_40, c_234])).
% 3.49/1.68  tff(c_244, plain, (![D_34]: (D_34='#skF_4'('#skF_6') | k1_funct_1('#skF_6', D_34)!=k1_funct_1('#skF_6', '#skF_3'('#skF_6')) | ~r2_hidden(D_34, '#skF_5') | ~r2_hidden('#skF_4'('#skF_6'), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_61, c_243])).
% 3.49/1.68  tff(c_339, plain, (~r2_hidden('#skF_4'('#skF_6'), '#skF_5')), inference(splitLeft, [status(thm)], [c_244])).
% 3.49/1.68  tff(c_342, plain, (~r1_tarski(k1_relat_1('#skF_6'), '#skF_5') | v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_181, c_339])).
% 3.49/1.68  tff(c_345, plain, (~r1_tarski(k1_relat_1('#skF_6'), '#skF_5') | v2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_40, c_342])).
% 3.49/1.68  tff(c_346, plain, (~r1_tarski(k1_relat_1('#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_61, c_345])).
% 3.49/1.68  tff(c_349, plain, (~v4_relat_1('#skF_6', '#skF_5') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_16, c_346])).
% 3.49/1.68  tff(c_356, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_91, c_349])).
% 3.49/1.68  tff(c_358, plain, (r2_hidden('#skF_4'('#skF_6'), '#skF_5')), inference(splitRight, [status(thm)], [c_244])).
% 3.49/1.68  tff(c_231, plain, (![C_33]: (C_33='#skF_4'('#skF_6') | k1_funct_1('#skF_6', C_33)!=k1_funct_1('#skF_6', '#skF_3'('#skF_6')) | ~r2_hidden('#skF_4'('#skF_6'), '#skF_5') | ~r2_hidden(C_33, '#skF_5') | v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_225, c_130])).
% 3.49/1.68  tff(c_240, plain, (![C_33]: (C_33='#skF_4'('#skF_6') | k1_funct_1('#skF_6', C_33)!=k1_funct_1('#skF_6', '#skF_3'('#skF_6')) | ~r2_hidden('#skF_4'('#skF_6'), '#skF_5') | ~r2_hidden(C_33, '#skF_5') | v2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_40, c_231])).
% 3.49/1.68  tff(c_241, plain, (![C_33]: (C_33='#skF_4'('#skF_6') | k1_funct_1('#skF_6', C_33)!=k1_funct_1('#skF_6', '#skF_3'('#skF_6')) | ~r2_hidden('#skF_4'('#skF_6'), '#skF_5') | ~r2_hidden(C_33, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_61, c_240])).
% 3.49/1.68  tff(c_359, plain, (~r2_hidden('#skF_4'('#skF_6'), '#skF_5')), inference(splitLeft, [status(thm)], [c_241])).
% 3.49/1.68  tff(c_368, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_358, c_359])).
% 3.49/1.68  tff(c_369, plain, (![C_33]: (C_33='#skF_4'('#skF_6') | k1_funct_1('#skF_6', C_33)!=k1_funct_1('#skF_6', '#skF_3'('#skF_6')) | ~r2_hidden(C_33, '#skF_5'))), inference(splitRight, [status(thm)], [c_241])).
% 3.49/1.68  tff(c_444, plain, ('#skF_4'('#skF_6')='#skF_3'('#skF_6') | ~r2_hidden('#skF_3'('#skF_6'), '#skF_5')), inference(reflexivity, [status(thm), theory('equality')], [c_369])).
% 3.49/1.68  tff(c_445, plain, (~r2_hidden('#skF_3'('#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_155, c_444])).
% 3.49/1.68  tff(c_457, plain, (~r1_tarski(k1_relat_1('#skF_6'), '#skF_5') | v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_172, c_445])).
% 3.49/1.68  tff(c_460, plain, (~r1_tarski(k1_relat_1('#skF_6'), '#skF_5') | v2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_40, c_457])).
% 3.49/1.68  tff(c_461, plain, (~r1_tarski(k1_relat_1('#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_61, c_460])).
% 3.49/1.68  tff(c_464, plain, (~v4_relat_1('#skF_6', '#skF_5') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_16, c_461])).
% 3.49/1.68  tff(c_471, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_91, c_464])).
% 3.49/1.68  tff(c_473, plain, (v2_funct_1('#skF_6')), inference(splitRight, [status(thm)], [c_42])).
% 3.49/1.68  tff(c_48, plain, (r2_hidden('#skF_7', '#skF_5') | ~v2_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.49/1.68  tff(c_475, plain, (r2_hidden('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_473, c_48])).
% 3.49/1.68  tff(c_476, plain, (![B_121, A_122]: (~r2_hidden(B_121, A_122) | ~v1_xboole_0(A_122))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.49/1.68  tff(c_480, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_475, c_476])).
% 3.49/1.68  tff(c_38, plain, (v1_funct_2('#skF_6', '#skF_5', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.49/1.68  tff(c_46, plain, (r2_hidden('#skF_8', '#skF_5') | ~v2_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.49/1.68  tff(c_482, plain, (r2_hidden('#skF_8', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_473, c_46])).
% 3.49/1.68  tff(c_836, plain, (![D_210, C_211, B_212, A_213]: (k1_funct_1(k2_funct_1(D_210), k1_funct_1(D_210, C_211))=C_211 | k1_xboole_0=B_212 | ~r2_hidden(C_211, A_213) | ~v2_funct_1(D_210) | ~m1_subset_1(D_210, k1_zfmisc_1(k2_zfmisc_1(A_213, B_212))) | ~v1_funct_2(D_210, A_213, B_212) | ~v1_funct_1(D_210))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.49/1.68  tff(c_915, plain, (![D_224, B_225]: (k1_funct_1(k2_funct_1(D_224), k1_funct_1(D_224, '#skF_8'))='#skF_8' | k1_xboole_0=B_225 | ~v2_funct_1(D_224) | ~m1_subset_1(D_224, k1_zfmisc_1(k2_zfmisc_1('#skF_5', B_225))) | ~v1_funct_2(D_224, '#skF_5', B_225) | ~v1_funct_1(D_224))), inference(resolution, [status(thm)], [c_482, c_836])).
% 3.49/1.68  tff(c_917, plain, (k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', '#skF_8'))='#skF_8' | k1_xboole_0='#skF_5' | ~v2_funct_1('#skF_6') | ~v1_funct_2('#skF_6', '#skF_5', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_36, c_915])).
% 3.49/1.68  tff(c_920, plain, (k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', '#skF_8'))='#skF_8' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_473, c_917])).
% 3.49/1.68  tff(c_921, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_920])).
% 3.49/1.68  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.49/1.68  tff(c_924, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_921, c_12])).
% 3.49/1.68  tff(c_926, plain, $false, inference(negUnitSimplification, [status(thm)], [c_480, c_924])).
% 3.49/1.68  tff(c_928, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_920])).
% 3.49/1.68  tff(c_472, plain, ('#skF_7'!='#skF_8'), inference(splitRight, [status(thm)], [c_42])).
% 3.49/1.68  tff(c_927, plain, (k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', '#skF_8'))='#skF_8'), inference(splitRight, [status(thm)], [c_920])).
% 3.49/1.68  tff(c_44, plain, (k1_funct_1('#skF_6', '#skF_7')=k1_funct_1('#skF_6', '#skF_8') | ~v2_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.49/1.68  tff(c_511, plain, (k1_funct_1('#skF_6', '#skF_7')=k1_funct_1('#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_473, c_44])).
% 3.49/1.68  tff(c_947, plain, (![D_230, B_231]: (k1_funct_1(k2_funct_1(D_230), k1_funct_1(D_230, '#skF_7'))='#skF_7' | k1_xboole_0=B_231 | ~v2_funct_1(D_230) | ~m1_subset_1(D_230, k1_zfmisc_1(k2_zfmisc_1('#skF_5', B_231))) | ~v1_funct_2(D_230, '#skF_5', B_231) | ~v1_funct_1(D_230))), inference(resolution, [status(thm)], [c_475, c_836])).
% 3.49/1.68  tff(c_949, plain, (k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', '#skF_7'))='#skF_7' | k1_xboole_0='#skF_5' | ~v2_funct_1('#skF_6') | ~v1_funct_2('#skF_6', '#skF_5', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_36, c_947])).
% 3.49/1.68  tff(c_952, plain, ('#skF_7'='#skF_8' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_473, c_927, c_511, c_949])).
% 3.49/1.68  tff(c_954, plain, $false, inference(negUnitSimplification, [status(thm)], [c_928, c_472, c_952])).
% 3.49/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.68  
% 3.49/1.68  Inference rules
% 3.49/1.68  ----------------------
% 3.49/1.68  #Ref     : 4
% 3.49/1.68  #Sup     : 205
% 3.49/1.68  #Fact    : 0
% 3.49/1.68  #Define  : 0
% 3.49/1.68  #Split   : 7
% 3.49/1.68  #Chain   : 0
% 3.49/1.68  #Close   : 0
% 3.49/1.68  
% 3.49/1.68  Ordering : KBO
% 3.49/1.68  
% 3.49/1.68  Simplification rules
% 3.49/1.68  ----------------------
% 3.49/1.68  #Subsume      : 70
% 3.49/1.68  #Demod        : 52
% 3.49/1.68  #Tautology    : 36
% 3.49/1.68  #SimpNegUnit  : 10
% 3.49/1.68  #BackRed      : 3
% 3.49/1.68  
% 3.49/1.68  #Partial instantiations: 0
% 3.49/1.68  #Strategies tried      : 1
% 3.49/1.68  
% 3.49/1.68  Timing (in seconds)
% 3.49/1.68  ----------------------
% 3.49/1.68  Preprocessing        : 0.35
% 3.49/1.68  Parsing              : 0.16
% 3.49/1.68  CNF conversion       : 0.03
% 3.49/1.68  Main loop            : 0.47
% 3.49/1.68  Inferencing          : 0.18
% 3.49/1.68  Reduction            : 0.12
% 3.49/1.68  Demodulation         : 0.08
% 3.49/1.68  BG Simplification    : 0.03
% 3.49/1.68  Subsumption          : 0.10
% 3.49/1.68  Abstraction          : 0.02
% 3.49/1.68  MUC search           : 0.00
% 3.49/1.68  Cooper               : 0.00
% 3.49/1.68  Total                : 0.86
% 3.49/1.68  Index Insertion      : 0.00
% 3.49/1.68  Index Deletion       : 0.00
% 3.49/1.68  Index Matching       : 0.00
% 3.49/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
