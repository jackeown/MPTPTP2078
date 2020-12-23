%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:29 EST 2020

% Result     : Theorem 3.95s
% Output     : CNFRefutation 3.95s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 240 expanded)
%              Number of leaves         :   40 (  96 expanded)
%              Depth                    :   12
%              Number of atoms          :  156 ( 500 expanded)
%              Number of equality atoms :   65 ( 213 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_126,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_60,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_114,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_234,plain,(
    ! [C_67,A_68,B_69] :
      ( v1_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_238,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_234])).

tff(c_38,plain,(
    ! [A_17] :
      ( k1_relat_1(A_17) != k1_xboole_0
      | k1_xboole_0 = A_17
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_246,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_238,c_38])).

tff(c_265,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_246])).

tff(c_68,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_570,plain,(
    ! [B_124,A_125] :
      ( k1_tarski(k1_funct_1(B_124,A_125)) = k2_relat_1(B_124)
      | k1_tarski(A_125) != k1_relat_1(B_124)
      | ~ v1_funct_1(B_124)
      | ~ v1_relat_1(B_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_555,plain,(
    ! [A_119,B_120,C_121] :
      ( k2_relset_1(A_119,B_120,C_121) = k2_relat_1(C_121)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_559,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_555])).

tff(c_60,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') != k1_tarski(k1_funct_1('#skF_4','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_560,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_559,c_60])).

tff(c_576,plain,
    ( k1_tarski('#skF_2') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_570,c_560])).

tff(c_598,plain,(
    k1_tarski('#skF_2') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_68,c_576])).

tff(c_419,plain,(
    ! [C_101,A_102,B_103] :
      ( v4_relat_1(C_101,A_102)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_423,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_64,c_419])).

tff(c_321,plain,(
    ! [B_84,A_85] :
      ( r1_tarski(k1_relat_1(B_84),A_85)
      | ~ v4_relat_1(B_84,A_85)
      | ~ v1_relat_1(B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( k1_tarski(B_11) = A_10
      | k1_xboole_0 = A_10
      | ~ r1_tarski(A_10,k1_tarski(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1590,plain,(
    ! [B_172,B_173] :
      ( k1_tarski(B_172) = k1_relat_1(B_173)
      | k1_relat_1(B_173) = k1_xboole_0
      | ~ v4_relat_1(B_173,k1_tarski(B_172))
      | ~ v1_relat_1(B_173) ) ),
    inference(resolution,[status(thm)],[c_321,c_16])).

tff(c_1612,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_423,c_1590])).

tff(c_1628,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_1612])).

tff(c_1630,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_265,c_598,c_1628])).

tff(c_1631,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_246])).

tff(c_32,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1643,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1631,c_1631,c_32])).

tff(c_36,plain,(
    ! [A_17] :
      ( k2_relat_1(A_17) != k1_xboole_0
      | k1_xboole_0 = A_17
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_245,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_238,c_36])).

tff(c_264,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_245])).

tff(c_1633,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1631,c_264])).

tff(c_1673,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1643,c_1633])).

tff(c_1674,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_245])).

tff(c_1675,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_245])).

tff(c_1709,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1674,c_1675])).

tff(c_2078,plain,(
    ! [A_234,B_235,C_236] :
      ( k2_relset_1(A_234,B_235,C_236) = k2_relat_1(C_236)
      | ~ m1_subset_1(C_236,k1_zfmisc_1(k2_zfmisc_1(A_234,B_235))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2081,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_2078])).

tff(c_2083,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1709,c_2081])).

tff(c_2084,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2083,c_60])).

tff(c_10,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_186,plain,(
    ! [B_53,C_54,A_55] :
      ( r2_hidden(B_53,C_54)
      | ~ r1_tarski(k2_tarski(A_55,B_53),C_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_208,plain,(
    ! [B_57,A_58] : r2_hidden(B_57,k2_tarski(A_58,B_57)) ),
    inference(resolution,[status(thm)],[c_6,c_186])).

tff(c_211,plain,(
    ! [A_4] : r2_hidden(A_4,k1_tarski(A_4)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_208])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1687,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1674,c_62])).

tff(c_66,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_58,plain,(
    ! [D_38,C_37,A_35,B_36] :
      ( r2_hidden(k1_funct_1(D_38,C_37),k2_relset_1(A_35,B_36,D_38))
      | k1_xboole_0 = B_36
      | ~ r2_hidden(C_37,A_35)
      | ~ m1_subset_1(D_38,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36)))
      | ~ v1_funct_2(D_38,A_35,B_36)
      | ~ v1_funct_1(D_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_2256,plain,(
    ! [D_252,C_253,A_254,B_255] :
      ( r2_hidden(k1_funct_1(D_252,C_253),k2_relset_1(A_254,B_255,D_252))
      | B_255 = '#skF_4'
      | ~ r2_hidden(C_253,A_254)
      | ~ m1_subset_1(D_252,k1_zfmisc_1(k2_zfmisc_1(A_254,B_255)))
      | ~ v1_funct_2(D_252,A_254,B_255)
      | ~ v1_funct_1(D_252) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1674,c_58])).

tff(c_2265,plain,(
    ! [C_253] :
      ( r2_hidden(k1_funct_1('#skF_4',C_253),'#skF_4')
      | '#skF_3' = '#skF_4'
      | ~ r2_hidden(C_253,k1_tarski('#skF_2'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3')))
      | ~ v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2083,c_2256])).

tff(c_2275,plain,(
    ! [C_253] :
      ( r2_hidden(k1_funct_1('#skF_4',C_253),'#skF_4')
      | '#skF_3' = '#skF_4'
      | ~ r2_hidden(C_253,k1_tarski('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_2265])).

tff(c_2281,plain,(
    ! [C_256] :
      ( r2_hidden(k1_funct_1('#skF_4',C_256),'#skF_4')
      | ~ r2_hidden(C_256,k1_tarski('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1687,c_2275])).

tff(c_2006,plain,(
    ! [A_223,B_224,C_225] :
      ( r1_tarski(k2_tarski(A_223,B_224),C_225)
      | ~ r2_hidden(B_224,C_225)
      | ~ r2_hidden(A_223,C_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2050,plain,(
    ! [A_231,C_232] :
      ( r1_tarski(k1_tarski(A_231),C_232)
      | ~ r2_hidden(A_231,C_232)
      | ~ r2_hidden(A_231,C_232) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_2006])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_176,plain,(
    ! [B_51,A_52] :
      ( B_51 = A_52
      | ~ r1_tarski(B_51,A_52)
      | ~ r1_tarski(A_52,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_181,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_176])).

tff(c_1677,plain,(
    ! [A_3] :
      ( A_3 = '#skF_4'
      | ~ r1_tarski(A_3,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1674,c_1674,c_181])).

tff(c_2069,plain,(
    ! [A_231] :
      ( k1_tarski(A_231) = '#skF_4'
      | ~ r2_hidden(A_231,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2050,c_1677])).

tff(c_2300,plain,(
    ! [C_257] :
      ( k1_tarski(k1_funct_1('#skF_4',C_257)) = '#skF_4'
      | ~ r2_hidden(C_257,k1_tarski('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_2281,c_2069])).

tff(c_2312,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_211,c_2300])).

tff(c_2318,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2084,c_2312])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:15:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.95/1.73  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.95/1.74  
% 3.95/1.74  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.95/1.74  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.95/1.74  
% 3.95/1.74  %Foreground sorts:
% 3.95/1.74  
% 3.95/1.74  
% 3.95/1.74  %Background operators:
% 3.95/1.74  
% 3.95/1.74  
% 3.95/1.74  %Foreground operators:
% 3.95/1.74  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.95/1.74  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.95/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.95/1.74  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.95/1.74  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.95/1.74  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.95/1.74  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.95/1.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.95/1.74  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.95/1.74  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.95/1.74  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.95/1.74  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.95/1.74  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.95/1.74  tff('#skF_2', type, '#skF_2': $i).
% 3.95/1.74  tff('#skF_3', type, '#skF_3': $i).
% 3.95/1.74  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.95/1.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.95/1.74  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.95/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.95/1.74  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.95/1.74  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.95/1.74  tff('#skF_4', type, '#skF_4': $i).
% 3.95/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.95/1.74  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.95/1.74  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.95/1.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.95/1.74  
% 3.95/1.77  tff(f_126, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 3.95/1.77  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.95/1.77  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 3.95/1.77  tff(f_76, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 3.95/1.77  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.95/1.77  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.95/1.77  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.95/1.77  tff(f_45, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.95/1.77  tff(f_60, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.95/1.77  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.95/1.77  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.95/1.77  tff(f_51, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.95/1.77  tff(f_114, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_funct_2)).
% 3.95/1.77  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.95/1.77  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.95/1.77  tff(c_234, plain, (![C_67, A_68, B_69]: (v1_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.95/1.77  tff(c_238, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_234])).
% 3.95/1.77  tff(c_38, plain, (![A_17]: (k1_relat_1(A_17)!=k1_xboole_0 | k1_xboole_0=A_17 | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.95/1.77  tff(c_246, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_238, c_38])).
% 3.95/1.77  tff(c_265, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_246])).
% 3.95/1.77  tff(c_68, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.95/1.77  tff(c_570, plain, (![B_124, A_125]: (k1_tarski(k1_funct_1(B_124, A_125))=k2_relat_1(B_124) | k1_tarski(A_125)!=k1_relat_1(B_124) | ~v1_funct_1(B_124) | ~v1_relat_1(B_124))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.95/1.77  tff(c_555, plain, (![A_119, B_120, C_121]: (k2_relset_1(A_119, B_120, C_121)=k2_relat_1(C_121) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.95/1.77  tff(c_559, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_555])).
% 3.95/1.77  tff(c_60, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')!=k1_tarski(k1_funct_1('#skF_4', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.95/1.77  tff(c_560, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_559, c_60])).
% 3.95/1.77  tff(c_576, plain, (k1_tarski('#skF_2')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_570, c_560])).
% 3.95/1.77  tff(c_598, plain, (k1_tarski('#skF_2')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_238, c_68, c_576])).
% 3.95/1.77  tff(c_419, plain, (![C_101, A_102, B_103]: (v4_relat_1(C_101, A_102) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.95/1.77  tff(c_423, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_64, c_419])).
% 3.95/1.77  tff(c_321, plain, (![B_84, A_85]: (r1_tarski(k1_relat_1(B_84), A_85) | ~v4_relat_1(B_84, A_85) | ~v1_relat_1(B_84))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.95/1.77  tff(c_16, plain, (![B_11, A_10]: (k1_tarski(B_11)=A_10 | k1_xboole_0=A_10 | ~r1_tarski(A_10, k1_tarski(B_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.95/1.77  tff(c_1590, plain, (![B_172, B_173]: (k1_tarski(B_172)=k1_relat_1(B_173) | k1_relat_1(B_173)=k1_xboole_0 | ~v4_relat_1(B_173, k1_tarski(B_172)) | ~v1_relat_1(B_173))), inference(resolution, [status(thm)], [c_321, c_16])).
% 3.95/1.77  tff(c_1612, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_423, c_1590])).
% 3.95/1.77  tff(c_1628, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_238, c_1612])).
% 3.95/1.77  tff(c_1630, plain, $false, inference(negUnitSimplification, [status(thm)], [c_265, c_598, c_1628])).
% 3.95/1.77  tff(c_1631, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_246])).
% 3.95/1.77  tff(c_32, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.95/1.77  tff(c_1643, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1631, c_1631, c_32])).
% 3.95/1.77  tff(c_36, plain, (![A_17]: (k2_relat_1(A_17)!=k1_xboole_0 | k1_xboole_0=A_17 | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.95/1.77  tff(c_245, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_238, c_36])).
% 3.95/1.77  tff(c_264, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_245])).
% 3.95/1.77  tff(c_1633, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1631, c_264])).
% 3.95/1.77  tff(c_1673, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1643, c_1633])).
% 3.95/1.77  tff(c_1674, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_245])).
% 3.95/1.77  tff(c_1675, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_245])).
% 3.95/1.77  tff(c_1709, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1674, c_1675])).
% 3.95/1.77  tff(c_2078, plain, (![A_234, B_235, C_236]: (k2_relset_1(A_234, B_235, C_236)=k2_relat_1(C_236) | ~m1_subset_1(C_236, k1_zfmisc_1(k2_zfmisc_1(A_234, B_235))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.95/1.77  tff(c_2081, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_2078])).
% 3.95/1.77  tff(c_2083, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1709, c_2081])).
% 3.95/1.77  tff(c_2084, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2083, c_60])).
% 3.95/1.77  tff(c_10, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.95/1.77  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.95/1.77  tff(c_186, plain, (![B_53, C_54, A_55]: (r2_hidden(B_53, C_54) | ~r1_tarski(k2_tarski(A_55, B_53), C_54))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.95/1.77  tff(c_208, plain, (![B_57, A_58]: (r2_hidden(B_57, k2_tarski(A_58, B_57)))), inference(resolution, [status(thm)], [c_6, c_186])).
% 3.95/1.77  tff(c_211, plain, (![A_4]: (r2_hidden(A_4, k1_tarski(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_208])).
% 3.95/1.77  tff(c_62, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.95/1.77  tff(c_1687, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1674, c_62])).
% 3.95/1.77  tff(c_66, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.95/1.77  tff(c_58, plain, (![D_38, C_37, A_35, B_36]: (r2_hidden(k1_funct_1(D_38, C_37), k2_relset_1(A_35, B_36, D_38)) | k1_xboole_0=B_36 | ~r2_hidden(C_37, A_35) | ~m1_subset_1(D_38, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))) | ~v1_funct_2(D_38, A_35, B_36) | ~v1_funct_1(D_38))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.95/1.77  tff(c_2256, plain, (![D_252, C_253, A_254, B_255]: (r2_hidden(k1_funct_1(D_252, C_253), k2_relset_1(A_254, B_255, D_252)) | B_255='#skF_4' | ~r2_hidden(C_253, A_254) | ~m1_subset_1(D_252, k1_zfmisc_1(k2_zfmisc_1(A_254, B_255))) | ~v1_funct_2(D_252, A_254, B_255) | ~v1_funct_1(D_252))), inference(demodulation, [status(thm), theory('equality')], [c_1674, c_58])).
% 3.95/1.77  tff(c_2265, plain, (![C_253]: (r2_hidden(k1_funct_1('#skF_4', C_253), '#skF_4') | '#skF_3'='#skF_4' | ~r2_hidden(C_253, k1_tarski('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3'))) | ~v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3') | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2083, c_2256])).
% 3.95/1.77  tff(c_2275, plain, (![C_253]: (r2_hidden(k1_funct_1('#skF_4', C_253), '#skF_4') | '#skF_3'='#skF_4' | ~r2_hidden(C_253, k1_tarski('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_2265])).
% 3.95/1.77  tff(c_2281, plain, (![C_256]: (r2_hidden(k1_funct_1('#skF_4', C_256), '#skF_4') | ~r2_hidden(C_256, k1_tarski('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_1687, c_2275])).
% 3.95/1.77  tff(c_2006, plain, (![A_223, B_224, C_225]: (r1_tarski(k2_tarski(A_223, B_224), C_225) | ~r2_hidden(B_224, C_225) | ~r2_hidden(A_223, C_225))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.95/1.77  tff(c_2050, plain, (![A_231, C_232]: (r1_tarski(k1_tarski(A_231), C_232) | ~r2_hidden(A_231, C_232) | ~r2_hidden(A_231, C_232))), inference(superposition, [status(thm), theory('equality')], [c_10, c_2006])).
% 3.95/1.77  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.95/1.77  tff(c_176, plain, (![B_51, A_52]: (B_51=A_52 | ~r1_tarski(B_51, A_52) | ~r1_tarski(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.95/1.77  tff(c_181, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_176])).
% 3.95/1.77  tff(c_1677, plain, (![A_3]: (A_3='#skF_4' | ~r1_tarski(A_3, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1674, c_1674, c_181])).
% 3.95/1.77  tff(c_2069, plain, (![A_231]: (k1_tarski(A_231)='#skF_4' | ~r2_hidden(A_231, '#skF_4'))), inference(resolution, [status(thm)], [c_2050, c_1677])).
% 3.95/1.77  tff(c_2300, plain, (![C_257]: (k1_tarski(k1_funct_1('#skF_4', C_257))='#skF_4' | ~r2_hidden(C_257, k1_tarski('#skF_2')))), inference(resolution, [status(thm)], [c_2281, c_2069])).
% 3.95/1.77  tff(c_2312, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))='#skF_4'), inference(resolution, [status(thm)], [c_211, c_2300])).
% 3.95/1.77  tff(c_2318, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2084, c_2312])).
% 3.95/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.95/1.77  
% 3.95/1.77  Inference rules
% 3.95/1.77  ----------------------
% 3.95/1.77  #Ref     : 3
% 3.95/1.77  #Sup     : 521
% 3.95/1.77  #Fact    : 0
% 3.95/1.77  #Define  : 0
% 3.95/1.77  #Split   : 6
% 3.95/1.77  #Chain   : 0
% 3.95/1.77  #Close   : 0
% 3.95/1.77  
% 3.95/1.77  Ordering : KBO
% 3.95/1.77  
% 3.95/1.77  Simplification rules
% 3.95/1.77  ----------------------
% 3.95/1.77  #Subsume      : 122
% 3.95/1.77  #Demod        : 233
% 3.95/1.77  #Tautology    : 159
% 3.95/1.77  #SimpNegUnit  : 15
% 3.95/1.77  #BackRed      : 31
% 3.95/1.77  
% 3.95/1.77  #Partial instantiations: 0
% 3.95/1.77  #Strategies tried      : 1
% 3.95/1.77  
% 3.95/1.77  Timing (in seconds)
% 3.95/1.77  ----------------------
% 3.95/1.77  Preprocessing        : 0.35
% 3.95/1.77  Parsing              : 0.19
% 3.95/1.77  CNF conversion       : 0.02
% 3.95/1.77  Main loop            : 0.59
% 3.95/1.77  Inferencing          : 0.20
% 3.95/1.77  Reduction            : 0.19
% 3.95/1.77  Demodulation         : 0.13
% 3.95/1.77  BG Simplification    : 0.03
% 3.95/1.77  Subsumption          : 0.12
% 3.95/1.77  Abstraction          : 0.03
% 3.95/1.77  MUC search           : 0.00
% 3.95/1.77  Cooper               : 0.00
% 3.95/1.77  Total                : 0.99
% 3.95/1.77  Index Insertion      : 0.00
% 3.95/1.77  Index Deletion       : 0.00
% 3.95/1.77  Index Matching       : 0.00
% 3.95/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
