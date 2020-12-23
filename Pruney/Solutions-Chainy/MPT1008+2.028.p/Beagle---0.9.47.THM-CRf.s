%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:29 EST 2020

% Result     : Theorem 6.89s
% Output     : CNFRefutation 7.01s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 406 expanded)
%              Number of leaves         :   43 ( 150 expanded)
%              Depth                    :   14
%              Number of atoms          :  177 ( 852 expanded)
%              Number of equality atoms :   71 ( 345 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_134,negated_conjecture,(
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

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

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

tff(f_71,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_52,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_122,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

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

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_125,plain,(
    ! [C_63,A_64,B_65] :
      ( v1_relat_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_138,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_125])).

tff(c_68,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_42,plain,(
    ! [A_24] :
      ( k1_relat_1(A_24) != k1_xboole_0
      | k1_xboole_0 = A_24
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_147,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_138,c_42])).

tff(c_170,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_147])).

tff(c_324,plain,(
    ! [C_95,A_96,B_97] :
      ( v4_relat_1(C_95,A_96)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_337,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_64,c_324])).

tff(c_34,plain,(
    ! [B_23,A_22] :
      ( k7_relat_1(B_23,A_22) = B_23
      | ~ v4_relat_1(B_23,A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_348,plain,
    ( k7_relat_1('#skF_4',k1_tarski('#skF_2')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_337,c_34])).

tff(c_351,plain,(
    k7_relat_1('#skF_4',k1_tarski('#skF_2')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_348])).

tff(c_44,plain,(
    ! [B_26,A_25] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_26,A_25)),A_25)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_373,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),k1_tarski('#skF_2'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_351,c_44])).

tff(c_377,plain,(
    r1_tarski(k1_relat_1('#skF_4'),k1_tarski('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_373])).

tff(c_20,plain,(
    ! [B_15,A_14] :
      ( k1_tarski(B_15) = A_14
      | k1_xboole_0 = A_14
      | ~ r1_tarski(A_14,k1_tarski(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_381,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_377,c_20])).

tff(c_386,plain,(
    k1_tarski('#skF_2') = k1_relat_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_170,c_381])).

tff(c_768,plain,(
    ! [B_149,A_150] :
      ( k1_tarski(k1_funct_1(B_149,A_150)) = k2_relat_1(B_149)
      | k1_tarski(A_150) != k1_relat_1(B_149)
      | ~ v1_funct_1(B_149)
      | ~ v1_relat_1(B_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_394,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_386,c_64])).

tff(c_673,plain,(
    ! [A_136,B_137,C_138] :
      ( k2_relset_1(A_136,B_137,C_138) = k2_relat_1(C_138)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_688,plain,(
    k2_relset_1(k1_relat_1('#skF_4'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_394,c_673])).

tff(c_60,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') != k1_tarski(k1_funct_1('#skF_4','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_392,plain,(
    k2_relset_1(k1_relat_1('#skF_4'),'#skF_3','#skF_4') != k1_tarski(k1_funct_1('#skF_4','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_386,c_60])).

tff(c_724,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_688,c_392])).

tff(c_774,plain,
    ( k1_tarski('#skF_2') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_768,c_724])).

tff(c_785,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_68,c_386,c_774])).

tff(c_786,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_147])).

tff(c_40,plain,(
    ! [A_24] :
      ( k2_relat_1(A_24) != k1_xboole_0
      | k1_xboole_0 = A_24
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_146,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_138,c_40])).

tff(c_162,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_146])).

tff(c_788,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_786,c_162])).

tff(c_36,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_794,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_786,c_786,c_36])).

tff(c_808,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_788,c_794])).

tff(c_809,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_38,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_817,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_809,c_809,c_38])).

tff(c_810,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_841,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_809,c_810])).

tff(c_1307,plain,(
    ! [B_231,A_232] :
      ( k1_tarski(k1_funct_1(B_231,A_232)) = k2_relat_1(B_231)
      | k1_tarski(A_232) != k1_relat_1(B_231)
      | ~ v1_funct_1(B_231)
      | ~ v1_relat_1(B_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_26,plain,(
    ! [A_16] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_815,plain,(
    ! [A_16] : m1_subset_1('#skF_4',k1_zfmisc_1(A_16)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_809,c_26])).

tff(c_1260,plain,(
    ! [A_225,B_226,C_227] :
      ( k2_relset_1(A_225,B_226,C_227) = k2_relat_1(C_227)
      | ~ m1_subset_1(C_227,k1_zfmisc_1(k2_zfmisc_1(A_225,B_226))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1267,plain,(
    ! [A_225,B_226] : k2_relset_1(A_225,B_226,'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_815,c_1260])).

tff(c_1273,plain,(
    ! [A_225,B_226] : k2_relset_1(A_225,B_226,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_841,c_1267])).

tff(c_1275,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1273,c_60])).

tff(c_1313,plain,
    ( k2_relat_1('#skF_4') != '#skF_4'
    | k1_tarski('#skF_2') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1307,c_1275])).

tff(c_1322,plain,(
    k1_tarski('#skF_2') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_68,c_817,c_841,c_1313])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_818,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_809,c_62])).

tff(c_66,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_92,plain,(
    ! [A_50,B_51] :
      ( r1_tarski(A_50,B_51)
      | ~ m1_subset_1(A_50,k1_zfmisc_1(B_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_100,plain,(
    ! [A_16] : r1_tarski(k1_xboole_0,A_16) ),
    inference(resolution,[status(thm)],[c_26,c_92])).

tff(c_814,plain,(
    ! [A_16] : r1_tarski('#skF_4',A_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_809,c_100])).

tff(c_58,plain,(
    ! [D_43,C_42,A_40,B_41] :
      ( r2_hidden(k1_funct_1(D_43,C_42),k2_relset_1(A_40,B_41,D_43))
      | k1_xboole_0 = B_41
      | ~ r2_hidden(C_42,A_40)
      | ~ m1_subset_1(D_43,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41)))
      | ~ v1_funct_2(D_43,A_40,B_41)
      | ~ v1_funct_1(D_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1368,plain,(
    ! [D_238,C_239,A_240,B_241] :
      ( r2_hidden(k1_funct_1(D_238,C_239),k2_relset_1(A_240,B_241,D_238))
      | B_241 = '#skF_4'
      | ~ r2_hidden(C_239,A_240)
      | ~ m1_subset_1(D_238,k1_zfmisc_1(k2_zfmisc_1(A_240,B_241)))
      | ~ v1_funct_2(D_238,A_240,B_241)
      | ~ v1_funct_1(D_238) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_809,c_58])).

tff(c_48,plain,(
    ! [B_30,A_29] :
      ( ~ r1_tarski(B_30,A_29)
      | ~ r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_8573,plain,(
    ! [A_552,B_553,D_554,C_555] :
      ( ~ r1_tarski(k2_relset_1(A_552,B_553,D_554),k1_funct_1(D_554,C_555))
      | B_553 = '#skF_4'
      | ~ r2_hidden(C_555,A_552)
      | ~ m1_subset_1(D_554,k1_zfmisc_1(k2_zfmisc_1(A_552,B_553)))
      | ~ v1_funct_2(D_554,A_552,B_553)
      | ~ v1_funct_1(D_554) ) ),
    inference(resolution,[status(thm)],[c_1368,c_48])).

tff(c_8591,plain,(
    ! [C_555,B_226,A_225] :
      ( ~ r1_tarski('#skF_4',k1_funct_1('#skF_4',C_555))
      | B_226 = '#skF_4'
      | ~ r2_hidden(C_555,A_225)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_225,B_226)))
      | ~ v1_funct_2('#skF_4',A_225,B_226)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1273,c_8573])).

tff(c_8596,plain,(
    ! [B_556,C_557,A_558] :
      ( B_556 = '#skF_4'
      | ~ r2_hidden(C_557,A_558)
      | ~ v1_funct_2('#skF_4',A_558,B_556) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_815,c_814,c_8591])).

tff(c_8606,plain,(
    ! [B_559,A_560,B_561] :
      ( B_559 = '#skF_4'
      | ~ v1_funct_2('#skF_4',A_560,B_559)
      | r1_tarski(A_560,B_561) ) ),
    inference(resolution,[status(thm)],[c_6,c_8596])).

tff(c_8608,plain,(
    ! [B_561] :
      ( '#skF_3' = '#skF_4'
      | r1_tarski(k1_tarski('#skF_2'),B_561) ) ),
    inference(resolution,[status(thm)],[c_66,c_8606])).

tff(c_8612,plain,(
    ! [B_562] : r1_tarski(k1_tarski('#skF_2'),B_562) ),
    inference(negUnitSimplification,[status(thm)],[c_818,c_8608])).

tff(c_848,plain,(
    ! [A_153] : r1_tarski('#skF_4',A_153) ),
    inference(demodulation,[status(thm),theory(equality)],[c_809,c_100])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_851,plain,(
    ! [A_153] :
      ( A_153 = '#skF_4'
      | ~ r1_tarski(A_153,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_848,c_8])).

tff(c_8724,plain,(
    k1_tarski('#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_8612,c_851])).

tff(c_8779,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1322,c_8724])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:40:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.89/2.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.89/2.39  
% 6.89/2.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.89/2.39  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 6.89/2.39  
% 6.89/2.39  %Foreground sorts:
% 6.89/2.39  
% 6.89/2.39  
% 6.89/2.39  %Background operators:
% 6.89/2.39  
% 6.89/2.39  
% 6.89/2.39  %Foreground operators:
% 6.89/2.39  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.89/2.39  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.89/2.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.89/2.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.89/2.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.89/2.39  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.89/2.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.89/2.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.89/2.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.89/2.39  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.89/2.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.89/2.39  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.89/2.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.89/2.39  tff('#skF_2', type, '#skF_2': $i).
% 6.89/2.39  tff('#skF_3', type, '#skF_3': $i).
% 6.89/2.39  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.89/2.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.89/2.39  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.89/2.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.89/2.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.89/2.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.89/2.39  tff('#skF_4', type, '#skF_4': $i).
% 6.89/2.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.89/2.39  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.89/2.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.89/2.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.89/2.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.89/2.39  
% 7.01/2.41  tff(f_134, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 7.01/2.41  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.01/2.41  tff(f_79, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 7.01/2.41  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.01/2.41  tff(f_68, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 7.01/2.41  tff(f_83, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 7.01/2.41  tff(f_50, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 7.01/2.41  tff(f_91, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 7.01/2.41  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.01/2.41  tff(f_71, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 7.01/2.41  tff(f_52, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 7.01/2.41  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 7.01/2.41  tff(f_56, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.01/2.41  tff(f_122, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_funct_2)).
% 7.01/2.41  tff(f_96, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 7.01/2.41  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.01/2.41  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.01/2.41  tff(c_125, plain, (![C_63, A_64, B_65]: (v1_relat_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.01/2.41  tff(c_138, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_125])).
% 7.01/2.41  tff(c_68, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.01/2.41  tff(c_42, plain, (![A_24]: (k1_relat_1(A_24)!=k1_xboole_0 | k1_xboole_0=A_24 | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.01/2.41  tff(c_147, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_138, c_42])).
% 7.01/2.41  tff(c_170, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_147])).
% 7.01/2.41  tff(c_324, plain, (![C_95, A_96, B_97]: (v4_relat_1(C_95, A_96) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.01/2.41  tff(c_337, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_64, c_324])).
% 7.01/2.41  tff(c_34, plain, (![B_23, A_22]: (k7_relat_1(B_23, A_22)=B_23 | ~v4_relat_1(B_23, A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.01/2.41  tff(c_348, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_2'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_337, c_34])).
% 7.01/2.41  tff(c_351, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_2'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_138, c_348])).
% 7.01/2.41  tff(c_44, plain, (![B_26, A_25]: (r1_tarski(k1_relat_1(k7_relat_1(B_26, A_25)), A_25) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.01/2.41  tff(c_373, plain, (r1_tarski(k1_relat_1('#skF_4'), k1_tarski('#skF_2')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_351, c_44])).
% 7.01/2.41  tff(c_377, plain, (r1_tarski(k1_relat_1('#skF_4'), k1_tarski('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_373])).
% 7.01/2.41  tff(c_20, plain, (![B_15, A_14]: (k1_tarski(B_15)=A_14 | k1_xboole_0=A_14 | ~r1_tarski(A_14, k1_tarski(B_15)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.01/2.41  tff(c_381, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_377, c_20])).
% 7.01/2.41  tff(c_386, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_170, c_381])).
% 7.01/2.41  tff(c_768, plain, (![B_149, A_150]: (k1_tarski(k1_funct_1(B_149, A_150))=k2_relat_1(B_149) | k1_tarski(A_150)!=k1_relat_1(B_149) | ~v1_funct_1(B_149) | ~v1_relat_1(B_149))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.01/2.41  tff(c_394, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_386, c_64])).
% 7.01/2.41  tff(c_673, plain, (![A_136, B_137, C_138]: (k2_relset_1(A_136, B_137, C_138)=k2_relat_1(C_138) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.01/2.41  tff(c_688, plain, (k2_relset_1(k1_relat_1('#skF_4'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_394, c_673])).
% 7.01/2.41  tff(c_60, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')!=k1_tarski(k1_funct_1('#skF_4', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.01/2.41  tff(c_392, plain, (k2_relset_1(k1_relat_1('#skF_4'), '#skF_3', '#skF_4')!=k1_tarski(k1_funct_1('#skF_4', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_386, c_60])).
% 7.01/2.41  tff(c_724, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_688, c_392])).
% 7.01/2.41  tff(c_774, plain, (k1_tarski('#skF_2')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_768, c_724])).
% 7.01/2.41  tff(c_785, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_138, c_68, c_386, c_774])).
% 7.01/2.41  tff(c_786, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_147])).
% 7.01/2.41  tff(c_40, plain, (![A_24]: (k2_relat_1(A_24)!=k1_xboole_0 | k1_xboole_0=A_24 | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.01/2.41  tff(c_146, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_138, c_40])).
% 7.01/2.41  tff(c_162, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_146])).
% 7.01/2.41  tff(c_788, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_786, c_162])).
% 7.01/2.41  tff(c_36, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.01/2.41  tff(c_794, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_786, c_786, c_36])).
% 7.01/2.41  tff(c_808, plain, $false, inference(negUnitSimplification, [status(thm)], [c_788, c_794])).
% 7.01/2.41  tff(c_809, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_146])).
% 7.01/2.41  tff(c_38, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.01/2.41  tff(c_817, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_809, c_809, c_38])).
% 7.01/2.41  tff(c_810, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_146])).
% 7.01/2.41  tff(c_841, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_809, c_810])).
% 7.01/2.41  tff(c_1307, plain, (![B_231, A_232]: (k1_tarski(k1_funct_1(B_231, A_232))=k2_relat_1(B_231) | k1_tarski(A_232)!=k1_relat_1(B_231) | ~v1_funct_1(B_231) | ~v1_relat_1(B_231))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.01/2.41  tff(c_26, plain, (![A_16]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.01/2.41  tff(c_815, plain, (![A_16]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_16)))), inference(demodulation, [status(thm), theory('equality')], [c_809, c_26])).
% 7.01/2.41  tff(c_1260, plain, (![A_225, B_226, C_227]: (k2_relset_1(A_225, B_226, C_227)=k2_relat_1(C_227) | ~m1_subset_1(C_227, k1_zfmisc_1(k2_zfmisc_1(A_225, B_226))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.01/2.41  tff(c_1267, plain, (![A_225, B_226]: (k2_relset_1(A_225, B_226, '#skF_4')=k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_815, c_1260])).
% 7.01/2.41  tff(c_1273, plain, (![A_225, B_226]: (k2_relset_1(A_225, B_226, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_841, c_1267])).
% 7.01/2.41  tff(c_1275, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1273, c_60])).
% 7.01/2.41  tff(c_1313, plain, (k2_relat_1('#skF_4')!='#skF_4' | k1_tarski('#skF_2')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1307, c_1275])).
% 7.01/2.41  tff(c_1322, plain, (k1_tarski('#skF_2')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_138, c_68, c_817, c_841, c_1313])).
% 7.01/2.41  tff(c_62, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.01/2.41  tff(c_818, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_809, c_62])).
% 7.01/2.41  tff(c_66, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.01/2.41  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.01/2.41  tff(c_92, plain, (![A_50, B_51]: (r1_tarski(A_50, B_51) | ~m1_subset_1(A_50, k1_zfmisc_1(B_51)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.01/2.41  tff(c_100, plain, (![A_16]: (r1_tarski(k1_xboole_0, A_16))), inference(resolution, [status(thm)], [c_26, c_92])).
% 7.01/2.41  tff(c_814, plain, (![A_16]: (r1_tarski('#skF_4', A_16))), inference(demodulation, [status(thm), theory('equality')], [c_809, c_100])).
% 7.01/2.41  tff(c_58, plain, (![D_43, C_42, A_40, B_41]: (r2_hidden(k1_funct_1(D_43, C_42), k2_relset_1(A_40, B_41, D_43)) | k1_xboole_0=B_41 | ~r2_hidden(C_42, A_40) | ~m1_subset_1(D_43, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))) | ~v1_funct_2(D_43, A_40, B_41) | ~v1_funct_1(D_43))), inference(cnfTransformation, [status(thm)], [f_122])).
% 7.01/2.41  tff(c_1368, plain, (![D_238, C_239, A_240, B_241]: (r2_hidden(k1_funct_1(D_238, C_239), k2_relset_1(A_240, B_241, D_238)) | B_241='#skF_4' | ~r2_hidden(C_239, A_240) | ~m1_subset_1(D_238, k1_zfmisc_1(k2_zfmisc_1(A_240, B_241))) | ~v1_funct_2(D_238, A_240, B_241) | ~v1_funct_1(D_238))), inference(demodulation, [status(thm), theory('equality')], [c_809, c_58])).
% 7.01/2.41  tff(c_48, plain, (![B_30, A_29]: (~r1_tarski(B_30, A_29) | ~r2_hidden(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.01/2.41  tff(c_8573, plain, (![A_552, B_553, D_554, C_555]: (~r1_tarski(k2_relset_1(A_552, B_553, D_554), k1_funct_1(D_554, C_555)) | B_553='#skF_4' | ~r2_hidden(C_555, A_552) | ~m1_subset_1(D_554, k1_zfmisc_1(k2_zfmisc_1(A_552, B_553))) | ~v1_funct_2(D_554, A_552, B_553) | ~v1_funct_1(D_554))), inference(resolution, [status(thm)], [c_1368, c_48])).
% 7.01/2.41  tff(c_8591, plain, (![C_555, B_226, A_225]: (~r1_tarski('#skF_4', k1_funct_1('#skF_4', C_555)) | B_226='#skF_4' | ~r2_hidden(C_555, A_225) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_225, B_226))) | ~v1_funct_2('#skF_4', A_225, B_226) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1273, c_8573])).
% 7.01/2.41  tff(c_8596, plain, (![B_556, C_557, A_558]: (B_556='#skF_4' | ~r2_hidden(C_557, A_558) | ~v1_funct_2('#skF_4', A_558, B_556))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_815, c_814, c_8591])).
% 7.01/2.41  tff(c_8606, plain, (![B_559, A_560, B_561]: (B_559='#skF_4' | ~v1_funct_2('#skF_4', A_560, B_559) | r1_tarski(A_560, B_561))), inference(resolution, [status(thm)], [c_6, c_8596])).
% 7.01/2.41  tff(c_8608, plain, (![B_561]: ('#skF_3'='#skF_4' | r1_tarski(k1_tarski('#skF_2'), B_561))), inference(resolution, [status(thm)], [c_66, c_8606])).
% 7.01/2.41  tff(c_8612, plain, (![B_562]: (r1_tarski(k1_tarski('#skF_2'), B_562))), inference(negUnitSimplification, [status(thm)], [c_818, c_8608])).
% 7.01/2.41  tff(c_848, plain, (![A_153]: (r1_tarski('#skF_4', A_153))), inference(demodulation, [status(thm), theory('equality')], [c_809, c_100])).
% 7.01/2.41  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.01/2.41  tff(c_851, plain, (![A_153]: (A_153='#skF_4' | ~r1_tarski(A_153, '#skF_4'))), inference(resolution, [status(thm)], [c_848, c_8])).
% 7.01/2.41  tff(c_8724, plain, (k1_tarski('#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_8612, c_851])).
% 7.01/2.41  tff(c_8779, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1322, c_8724])).
% 7.01/2.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.01/2.41  
% 7.01/2.41  Inference rules
% 7.01/2.41  ----------------------
% 7.01/2.41  #Ref     : 0
% 7.01/2.41  #Sup     : 2035
% 7.01/2.41  #Fact    : 2
% 7.01/2.41  #Define  : 0
% 7.01/2.41  #Split   : 6
% 7.01/2.41  #Chain   : 0
% 7.01/2.41  #Close   : 0
% 7.01/2.41  
% 7.01/2.41  Ordering : KBO
% 7.01/2.41  
% 7.01/2.41  Simplification rules
% 7.01/2.41  ----------------------
% 7.01/2.41  #Subsume      : 739
% 7.01/2.41  #Demod        : 1678
% 7.01/2.41  #Tautology    : 735
% 7.01/2.41  #SimpNegUnit  : 7
% 7.01/2.41  #BackRed      : 38
% 7.01/2.41  
% 7.01/2.41  #Partial instantiations: 0
% 7.01/2.41  #Strategies tried      : 1
% 7.01/2.41  
% 7.01/2.41  Timing (in seconds)
% 7.01/2.41  ----------------------
% 7.01/2.41  Preprocessing        : 0.36
% 7.01/2.41  Parsing              : 0.19
% 7.01/2.41  CNF conversion       : 0.02
% 7.01/2.41  Main loop            : 1.28
% 7.01/2.41  Inferencing          : 0.42
% 7.01/2.41  Reduction            : 0.43
% 7.01/2.41  Demodulation         : 0.31
% 7.01/2.41  BG Simplification    : 0.04
% 7.01/2.41  Subsumption          : 0.30
% 7.01/2.41  Abstraction          : 0.06
% 7.01/2.41  MUC search           : 0.00
% 7.01/2.41  Cooper               : 0.00
% 7.01/2.41  Total                : 1.68
% 7.01/2.41  Index Insertion      : 0.00
% 7.01/2.41  Index Deletion       : 0.00
% 7.01/2.41  Index Matching       : 0.00
% 7.01/2.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
