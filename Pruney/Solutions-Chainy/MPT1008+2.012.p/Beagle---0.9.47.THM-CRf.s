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
% DateTime   : Thu Dec  3 10:14:27 EST 2020

% Result     : Theorem 5.10s
% Output     : CNFRefutation 5.10s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 393 expanded)
%              Number of leaves         :   51 ( 149 expanded)
%              Depth                    :   17
%              Number of atoms          :  216 ( 806 expanded)
%              Number of equality atoms :   91 ( 329 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_167,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_113,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_101,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_119,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_109,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_131,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_127,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_123,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_93,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_42,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_52,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_155,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

tff(c_94,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_261,plain,(
    ! [C_89,A_90,B_91] :
      ( v1_relat_1(C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_278,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_94,c_261])).

tff(c_62,plain,(
    ! [A_33] :
      ( k2_relat_1(A_33) != k1_xboole_0
      | k1_xboole_0 = A_33
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_298,plain,
    ( k2_relat_1('#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_278,c_62])).

tff(c_300,plain,(
    k2_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_298])).

tff(c_464,plain,(
    ! [C_122,A_123,B_124] :
      ( v4_relat_1(C_122,A_123)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_488,plain,(
    v4_relat_1('#skF_6',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_94,c_464])).

tff(c_56,plain,(
    ! [B_32,A_31] :
      ( k7_relat_1(B_32,A_31) = B_32
      | ~ v4_relat_1(B_32,A_31)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_499,plain,
    ( k7_relat_1('#skF_6',k1_tarski('#skF_4')) = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_488,c_56])).

tff(c_502,plain,(
    k7_relat_1('#skF_6',k1_tarski('#skF_4')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_499])).

tff(c_50,plain,(
    ! [B_28,A_27] :
      ( k2_relat_1(k7_relat_1(B_28,A_27)) = k9_relat_1(B_28,A_27)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_571,plain,
    ( k9_relat_1('#skF_6',k1_tarski('#skF_4')) = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_502,c_50])).

tff(c_575,plain,(
    k9_relat_1('#skF_6',k1_tarski('#skF_4')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_571])).

tff(c_46,plain,(
    ! [A_22,B_24] :
      ( k9_relat_1(A_22,k1_tarski(B_24)) = k11_relat_1(A_22,B_24)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_581,plain,
    ( k11_relat_1('#skF_6','#skF_4') = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_575,c_46])).

tff(c_588,plain,(
    k11_relat_1('#skF_6','#skF_4') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_581])).

tff(c_52,plain,(
    ! [A_29,B_30] :
      ( r2_hidden(A_29,k1_relat_1(B_30))
      | k11_relat_1(B_30,A_29) = k1_xboole_0
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_281,plain,(
    ! [A_92,B_93] :
      ( m1_subset_1(k1_tarski(A_92),k1_zfmisc_1(B_93))
      | ~ r2_hidden(A_92,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_40,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(A_17,B_18)
      | ~ m1_subset_1(A_17,k1_zfmisc_1(B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_290,plain,(
    ! [A_92,B_93] :
      ( r1_tarski(k1_tarski(A_92),B_93)
      | ~ r2_hidden(A_92,B_93) ) ),
    inference(resolution,[status(thm)],[c_281,c_40])).

tff(c_98,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_1017,plain,(
    ! [B_200,A_201] :
      ( k1_tarski(k1_funct_1(B_200,A_201)) = k2_relat_1(B_200)
      | k1_tarski(A_201) != k1_relat_1(B_200)
      | ~ v1_funct_1(B_200)
      | ~ v1_relat_1(B_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_895,plain,(
    ! [A_187,B_188,C_189] :
      ( k2_relset_1(A_187,B_188,C_189) = k2_relat_1(C_189)
      | ~ m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1(A_187,B_188))) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_919,plain,(
    k2_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_94,c_895])).

tff(c_90,plain,(
    k2_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') != k1_tarski(k1_funct_1('#skF_6','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_929,plain,(
    k1_tarski(k1_funct_1('#skF_6','#skF_4')) != k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_919,c_90])).

tff(c_1023,plain,
    ( k1_tarski('#skF_4') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1017,c_929])).

tff(c_1050,plain,(
    k1_tarski('#skF_4') != k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_98,c_1023])).

tff(c_853,plain,(
    ! [A_179,B_180,C_181] :
      ( k1_relset_1(A_179,B_180,C_181) = k1_relat_1(C_181)
      | ~ m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(A_179,B_180))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_877,plain,(
    k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_94,c_853])).

tff(c_934,plain,(
    ! [A_192,B_193,C_194] :
      ( m1_subset_1(k1_relset_1(A_192,B_193,C_194),k1_zfmisc_1(A_192))
      | ~ m1_subset_1(C_194,k1_zfmisc_1(k2_zfmisc_1(A_192,B_193))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_972,plain,
    ( m1_subset_1(k1_relat_1('#skF_6'),k1_zfmisc_1(k1_tarski('#skF_4')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_877,c_934])).

tff(c_990,plain,(
    m1_subset_1(k1_relat_1('#skF_6'),k1_zfmisc_1(k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_972])).

tff(c_999,plain,(
    r1_tarski(k1_relat_1('#skF_6'),k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_990,c_40])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1002,plain,
    ( k1_tarski('#skF_4') = k1_relat_1('#skF_6')
    | ~ r1_tarski(k1_tarski('#skF_4'),k1_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_999,c_2])).

tff(c_1070,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),k1_relat_1('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_1050,c_1002])).

tff(c_1074,plain,(
    ~ r2_hidden('#skF_4',k1_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_290,c_1070])).

tff(c_1077,plain,
    ( k11_relat_1('#skF_6','#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_1074])).

tff(c_1080,plain,(
    k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_588,c_1077])).

tff(c_1082,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_300,c_1080])).

tff(c_1083,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_298])).

tff(c_60,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1097,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1083,c_1083,c_60])).

tff(c_64,plain,(
    ! [A_33] :
      ( k1_relat_1(A_33) != k1_xboole_0
      | k1_xboole_0 = A_33
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_297,plain,
    ( k1_relat_1('#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_278,c_64])).

tff(c_299,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_297])).

tff(c_1085,plain,(
    k1_relat_1('#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1083,c_299])).

tff(c_1128,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1097,c_1085])).

tff(c_1129,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_297])).

tff(c_92,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_1189,plain,(
    '#skF_5' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1129,c_92])).

tff(c_96,plain,(
    v1_funct_2('#skF_6',k1_tarski('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_151,plain,(
    ! [A_74] : k2_tarski(A_74,A_74) = k1_tarski(A_74) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_12,plain,(
    ! [D_8,B_4] : r2_hidden(D_8,k2_tarski(D_8,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_157,plain,(
    ! [A_74] : r2_hidden(A_74,k1_tarski(A_74)) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_12])).

tff(c_1622,plain,(
    ! [A_273,B_274] :
      ( k9_relat_1(A_273,k1_tarski(B_274)) = k11_relat_1(A_273,B_274)
      | ~ v1_relat_1(A_273) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_58,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1142,plain,(
    k2_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1129,c_1129,c_58])).

tff(c_1131,plain,(
    k2_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_298])).

tff(c_1174,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1142,c_1129,c_1131])).

tff(c_1176,plain,(
    k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_298])).

tff(c_1197,plain,(
    k2_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1129,c_1176])).

tff(c_36,plain,(
    ! [A_14] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1184,plain,(
    ! [A_14] : m1_subset_1('#skF_6',k1_zfmisc_1(A_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1129,c_36])).

tff(c_1396,plain,(
    ! [C_234,A_235,B_236] :
      ( v4_relat_1(C_234,A_235)
      | ~ m1_subset_1(C_234,k1_zfmisc_1(k2_zfmisc_1(A_235,B_236))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1415,plain,(
    ! [A_235] : v4_relat_1('#skF_6',A_235) ),
    inference(resolution,[status(thm)],[c_1184,c_1396])).

tff(c_1460,plain,(
    ! [B_240,A_241] :
      ( k7_relat_1(B_240,A_241) = B_240
      | ~ v4_relat_1(B_240,A_241)
      | ~ v1_relat_1(B_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1463,plain,(
    ! [A_235] :
      ( k7_relat_1('#skF_6',A_235) = '#skF_6'
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1415,c_1460])).

tff(c_1466,plain,(
    ! [A_235] : k7_relat_1('#skF_6',A_235) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_1463])).

tff(c_1563,plain,(
    ! [B_265,A_266] :
      ( k2_relat_1(k7_relat_1(B_265,A_266)) = k9_relat_1(B_265,A_266)
      | ~ v1_relat_1(B_265) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1572,plain,(
    ! [A_235] :
      ( k9_relat_1('#skF_6',A_235) = k2_relat_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1466,c_1563])).

tff(c_1576,plain,(
    ! [A_235] : k9_relat_1('#skF_6',A_235) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_1197,c_1572])).

tff(c_1629,plain,(
    ! [B_274] :
      ( k11_relat_1('#skF_6',B_274) = '#skF_6'
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1622,c_1576])).

tff(c_1639,plain,(
    ! [B_274] : k11_relat_1('#skF_6',B_274) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_1629])).

tff(c_1188,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1129,c_1129,c_60])).

tff(c_54,plain,(
    ! [B_30,A_29] :
      ( k11_relat_1(B_30,A_29) != k1_xboole_0
      | ~ r2_hidden(A_29,k1_relat_1(B_30))
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1736,plain,(
    ! [B_290,A_291] :
      ( k11_relat_1(B_290,A_291) != '#skF_6'
      | ~ r2_hidden(A_291,k1_relat_1(B_290))
      | ~ v1_relat_1(B_290) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1129,c_54])).

tff(c_1742,plain,(
    ! [A_291] :
      ( k11_relat_1('#skF_6',A_291) != '#skF_6'
      | ~ r2_hidden(A_291,'#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1188,c_1736])).

tff(c_1748,plain,(
    ! [A_291] : ~ r2_hidden(A_291,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_1639,c_1742])).

tff(c_1876,plain,(
    ! [A_322,B_323,C_324] :
      ( k2_relset_1(A_322,B_323,C_324) = k2_relat_1(C_324)
      | ~ m1_subset_1(C_324,k1_zfmisc_1(k2_zfmisc_1(A_322,B_323))) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1880,plain,(
    ! [A_322,B_323] : k2_relset_1(A_322,B_323,'#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1184,c_1876])).

tff(c_1896,plain,(
    ! [A_322,B_323] : k2_relset_1(A_322,B_323,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1197,c_1880])).

tff(c_88,plain,(
    ! [D_60,C_59,A_57,B_58] :
      ( r2_hidden(k1_funct_1(D_60,C_59),k2_relset_1(A_57,B_58,D_60))
      | k1_xboole_0 = B_58
      | ~ r2_hidden(C_59,A_57)
      | ~ m1_subset_1(D_60,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58)))
      | ~ v1_funct_2(D_60,A_57,B_58)
      | ~ v1_funct_1(D_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_4111,plain,(
    ! [D_7890,C_7891,A_7892,B_7893] :
      ( r2_hidden(k1_funct_1(D_7890,C_7891),k2_relset_1(A_7892,B_7893,D_7890))
      | B_7893 = '#skF_6'
      | ~ r2_hidden(C_7891,A_7892)
      | ~ m1_subset_1(D_7890,k1_zfmisc_1(k2_zfmisc_1(A_7892,B_7893)))
      | ~ v1_funct_2(D_7890,A_7892,B_7893)
      | ~ v1_funct_1(D_7890) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1129,c_88])).

tff(c_4126,plain,(
    ! [C_7891,B_323,A_322] :
      ( r2_hidden(k1_funct_1('#skF_6',C_7891),'#skF_6')
      | B_323 = '#skF_6'
      | ~ r2_hidden(C_7891,A_322)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_322,B_323)))
      | ~ v1_funct_2('#skF_6',A_322,B_323)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1896,c_4111])).

tff(c_4134,plain,(
    ! [C_7891,B_323,A_322] :
      ( r2_hidden(k1_funct_1('#skF_6',C_7891),'#skF_6')
      | B_323 = '#skF_6'
      | ~ r2_hidden(C_7891,A_322)
      | ~ v1_funct_2('#skF_6',A_322,B_323) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_1184,c_4126])).

tff(c_4138,plain,(
    ! [B_7958,C_7959,A_7960] :
      ( B_7958 = '#skF_6'
      | ~ r2_hidden(C_7959,A_7960)
      | ~ v1_funct_2('#skF_6',A_7960,B_7958) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1748,c_4134])).

tff(c_4157,plain,(
    ! [B_8025,A_8026] :
      ( B_8025 = '#skF_6'
      | ~ v1_funct_2('#skF_6',k1_tarski(A_8026),B_8025) ) ),
    inference(resolution,[status(thm)],[c_157,c_4138])).

tff(c_4164,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_96,c_4157])).

tff(c_4168,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1189,c_4164])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:04:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.10/1.94  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.10/1.95  
% 5.10/1.95  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.10/1.95  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 5.10/1.95  
% 5.10/1.95  %Foreground sorts:
% 5.10/1.95  
% 5.10/1.95  
% 5.10/1.95  %Background operators:
% 5.10/1.95  
% 5.10/1.95  
% 5.10/1.95  %Foreground operators:
% 5.10/1.95  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.10/1.95  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.10/1.95  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.10/1.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.10/1.95  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.10/1.95  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.10/1.95  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.10/1.95  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.10/1.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.10/1.95  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.10/1.95  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.10/1.95  tff('#skF_5', type, '#skF_5': $i).
% 5.10/1.95  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.10/1.95  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 5.10/1.95  tff('#skF_6', type, '#skF_6': $i).
% 5.10/1.95  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.10/1.95  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.10/1.95  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.10/1.95  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.10/1.95  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.10/1.95  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.10/1.95  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.10/1.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.10/1.95  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.10/1.95  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.10/1.95  tff('#skF_4', type, '#skF_4': $i).
% 5.10/1.95  tff('#skF_3', type, '#skF_3': $i > $i).
% 5.10/1.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.10/1.95  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.10/1.95  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.10/1.95  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.10/1.95  
% 5.10/1.97  tff(f_167, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_2)).
% 5.10/1.97  tff(f_113, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.10/1.97  tff(f_101, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 5.10/1.97  tff(f_119, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.10/1.97  tff(f_90, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 5.10/1.97  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 5.10/1.97  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 5.10/1.97  tff(f_84, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 5.10/1.97  tff(f_56, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 5.10/1.97  tff(f_60, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.10/1.97  tff(f_109, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 5.10/1.97  tff(f_131, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.10/1.97  tff(f_127, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.10/1.97  tff(f_123, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 5.10/1.97  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.10/1.97  tff(f_93, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 5.10/1.97  tff(f_42, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 5.10/1.97  tff(f_40, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 5.10/1.97  tff(f_52, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 5.10/1.97  tff(f_155, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 5.10/1.97  tff(c_94, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_167])).
% 5.10/1.97  tff(c_261, plain, (![C_89, A_90, B_91]: (v1_relat_1(C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.10/1.97  tff(c_278, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_94, c_261])).
% 5.10/1.97  tff(c_62, plain, (![A_33]: (k2_relat_1(A_33)!=k1_xboole_0 | k1_xboole_0=A_33 | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.10/1.97  tff(c_298, plain, (k2_relat_1('#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_278, c_62])).
% 5.10/1.97  tff(c_300, plain, (k2_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_298])).
% 5.10/1.97  tff(c_464, plain, (![C_122, A_123, B_124]: (v4_relat_1(C_122, A_123) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.10/1.97  tff(c_488, plain, (v4_relat_1('#skF_6', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_94, c_464])).
% 5.10/1.97  tff(c_56, plain, (![B_32, A_31]: (k7_relat_1(B_32, A_31)=B_32 | ~v4_relat_1(B_32, A_31) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.10/1.97  tff(c_499, plain, (k7_relat_1('#skF_6', k1_tarski('#skF_4'))='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_488, c_56])).
% 5.10/1.97  tff(c_502, plain, (k7_relat_1('#skF_6', k1_tarski('#skF_4'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_278, c_499])).
% 5.10/1.97  tff(c_50, plain, (![B_28, A_27]: (k2_relat_1(k7_relat_1(B_28, A_27))=k9_relat_1(B_28, A_27) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.10/1.97  tff(c_571, plain, (k9_relat_1('#skF_6', k1_tarski('#skF_4'))=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_502, c_50])).
% 5.10/1.97  tff(c_575, plain, (k9_relat_1('#skF_6', k1_tarski('#skF_4'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_278, c_571])).
% 5.10/1.97  tff(c_46, plain, (![A_22, B_24]: (k9_relat_1(A_22, k1_tarski(B_24))=k11_relat_1(A_22, B_24) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.10/1.97  tff(c_581, plain, (k11_relat_1('#skF_6', '#skF_4')=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_575, c_46])).
% 5.10/1.97  tff(c_588, plain, (k11_relat_1('#skF_6', '#skF_4')=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_278, c_581])).
% 5.10/1.97  tff(c_52, plain, (![A_29, B_30]: (r2_hidden(A_29, k1_relat_1(B_30)) | k11_relat_1(B_30, A_29)=k1_xboole_0 | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.10/1.97  tff(c_281, plain, (![A_92, B_93]: (m1_subset_1(k1_tarski(A_92), k1_zfmisc_1(B_93)) | ~r2_hidden(A_92, B_93))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.10/1.97  tff(c_40, plain, (![A_17, B_18]: (r1_tarski(A_17, B_18) | ~m1_subset_1(A_17, k1_zfmisc_1(B_18)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.10/1.97  tff(c_290, plain, (![A_92, B_93]: (r1_tarski(k1_tarski(A_92), B_93) | ~r2_hidden(A_92, B_93))), inference(resolution, [status(thm)], [c_281, c_40])).
% 5.10/1.97  tff(c_98, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_167])).
% 5.10/1.97  tff(c_1017, plain, (![B_200, A_201]: (k1_tarski(k1_funct_1(B_200, A_201))=k2_relat_1(B_200) | k1_tarski(A_201)!=k1_relat_1(B_200) | ~v1_funct_1(B_200) | ~v1_relat_1(B_200))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.10/1.97  tff(c_895, plain, (![A_187, B_188, C_189]: (k2_relset_1(A_187, B_188, C_189)=k2_relat_1(C_189) | ~m1_subset_1(C_189, k1_zfmisc_1(k2_zfmisc_1(A_187, B_188))))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.10/1.97  tff(c_919, plain, (k2_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_94, c_895])).
% 5.10/1.97  tff(c_90, plain, (k2_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')!=k1_tarski(k1_funct_1('#skF_6', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_167])).
% 5.10/1.97  tff(c_929, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_4'))!=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_919, c_90])).
% 5.10/1.97  tff(c_1023, plain, (k1_tarski('#skF_4')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1017, c_929])).
% 5.10/1.97  tff(c_1050, plain, (k1_tarski('#skF_4')!=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_278, c_98, c_1023])).
% 5.10/1.97  tff(c_853, plain, (![A_179, B_180, C_181]: (k1_relset_1(A_179, B_180, C_181)=k1_relat_1(C_181) | ~m1_subset_1(C_181, k1_zfmisc_1(k2_zfmisc_1(A_179, B_180))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.10/1.97  tff(c_877, plain, (k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_94, c_853])).
% 5.10/1.97  tff(c_934, plain, (![A_192, B_193, C_194]: (m1_subset_1(k1_relset_1(A_192, B_193, C_194), k1_zfmisc_1(A_192)) | ~m1_subset_1(C_194, k1_zfmisc_1(k2_zfmisc_1(A_192, B_193))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.10/1.97  tff(c_972, plain, (m1_subset_1(k1_relat_1('#skF_6'), k1_zfmisc_1(k1_tarski('#skF_4'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_877, c_934])).
% 5.10/1.97  tff(c_990, plain, (m1_subset_1(k1_relat_1('#skF_6'), k1_zfmisc_1(k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_972])).
% 5.10/1.97  tff(c_999, plain, (r1_tarski(k1_relat_1('#skF_6'), k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_990, c_40])).
% 5.10/1.97  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.10/1.97  tff(c_1002, plain, (k1_tarski('#skF_4')=k1_relat_1('#skF_6') | ~r1_tarski(k1_tarski('#skF_4'), k1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_999, c_2])).
% 5.10/1.97  tff(c_1070, plain, (~r1_tarski(k1_tarski('#skF_4'), k1_relat_1('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_1050, c_1002])).
% 5.10/1.97  tff(c_1074, plain, (~r2_hidden('#skF_4', k1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_290, c_1070])).
% 5.10/1.97  tff(c_1077, plain, (k11_relat_1('#skF_6', '#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_52, c_1074])).
% 5.10/1.97  tff(c_1080, plain, (k2_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_278, c_588, c_1077])).
% 5.10/1.97  tff(c_1082, plain, $false, inference(negUnitSimplification, [status(thm)], [c_300, c_1080])).
% 5.10/1.97  tff(c_1083, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_298])).
% 5.10/1.97  tff(c_60, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.10/1.97  tff(c_1097, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1083, c_1083, c_60])).
% 5.10/1.97  tff(c_64, plain, (![A_33]: (k1_relat_1(A_33)!=k1_xboole_0 | k1_xboole_0=A_33 | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.10/1.97  tff(c_297, plain, (k1_relat_1('#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_278, c_64])).
% 5.10/1.97  tff(c_299, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_297])).
% 5.10/1.97  tff(c_1085, plain, (k1_relat_1('#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1083, c_299])).
% 5.10/1.97  tff(c_1128, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1097, c_1085])).
% 5.10/1.97  tff(c_1129, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_297])).
% 5.10/1.97  tff(c_92, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_167])).
% 5.10/1.97  tff(c_1189, plain, ('#skF_5'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1129, c_92])).
% 5.10/1.97  tff(c_96, plain, (v1_funct_2('#skF_6', k1_tarski('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_167])).
% 5.10/1.97  tff(c_151, plain, (![A_74]: (k2_tarski(A_74, A_74)=k1_tarski(A_74))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.10/1.97  tff(c_12, plain, (![D_8, B_4]: (r2_hidden(D_8, k2_tarski(D_8, B_4)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.10/1.97  tff(c_157, plain, (![A_74]: (r2_hidden(A_74, k1_tarski(A_74)))), inference(superposition, [status(thm), theory('equality')], [c_151, c_12])).
% 5.10/1.97  tff(c_1622, plain, (![A_273, B_274]: (k9_relat_1(A_273, k1_tarski(B_274))=k11_relat_1(A_273, B_274) | ~v1_relat_1(A_273))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.10/1.97  tff(c_58, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.10/1.97  tff(c_1142, plain, (k2_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1129, c_1129, c_58])).
% 5.10/1.97  tff(c_1131, plain, (k2_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_298])).
% 5.10/1.97  tff(c_1174, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1142, c_1129, c_1131])).
% 5.10/1.97  tff(c_1176, plain, (k2_relat_1('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_298])).
% 5.10/1.97  tff(c_1197, plain, (k2_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1129, c_1176])).
% 5.10/1.97  tff(c_36, plain, (![A_14]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.10/1.97  tff(c_1184, plain, (![A_14]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_1129, c_36])).
% 5.10/1.97  tff(c_1396, plain, (![C_234, A_235, B_236]: (v4_relat_1(C_234, A_235) | ~m1_subset_1(C_234, k1_zfmisc_1(k2_zfmisc_1(A_235, B_236))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.10/1.97  tff(c_1415, plain, (![A_235]: (v4_relat_1('#skF_6', A_235))), inference(resolution, [status(thm)], [c_1184, c_1396])).
% 5.10/1.97  tff(c_1460, plain, (![B_240, A_241]: (k7_relat_1(B_240, A_241)=B_240 | ~v4_relat_1(B_240, A_241) | ~v1_relat_1(B_240))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.10/1.97  tff(c_1463, plain, (![A_235]: (k7_relat_1('#skF_6', A_235)='#skF_6' | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_1415, c_1460])).
% 5.10/1.97  tff(c_1466, plain, (![A_235]: (k7_relat_1('#skF_6', A_235)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_278, c_1463])).
% 5.10/1.97  tff(c_1563, plain, (![B_265, A_266]: (k2_relat_1(k7_relat_1(B_265, A_266))=k9_relat_1(B_265, A_266) | ~v1_relat_1(B_265))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.10/1.97  tff(c_1572, plain, (![A_235]: (k9_relat_1('#skF_6', A_235)=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1466, c_1563])).
% 5.10/1.97  tff(c_1576, plain, (![A_235]: (k9_relat_1('#skF_6', A_235)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_278, c_1197, c_1572])).
% 5.10/1.97  tff(c_1629, plain, (![B_274]: (k11_relat_1('#skF_6', B_274)='#skF_6' | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1622, c_1576])).
% 5.10/1.97  tff(c_1639, plain, (![B_274]: (k11_relat_1('#skF_6', B_274)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_278, c_1629])).
% 5.10/1.97  tff(c_1188, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1129, c_1129, c_60])).
% 5.10/1.97  tff(c_54, plain, (![B_30, A_29]: (k11_relat_1(B_30, A_29)!=k1_xboole_0 | ~r2_hidden(A_29, k1_relat_1(B_30)) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.10/1.97  tff(c_1736, plain, (![B_290, A_291]: (k11_relat_1(B_290, A_291)!='#skF_6' | ~r2_hidden(A_291, k1_relat_1(B_290)) | ~v1_relat_1(B_290))), inference(demodulation, [status(thm), theory('equality')], [c_1129, c_54])).
% 5.10/1.97  tff(c_1742, plain, (![A_291]: (k11_relat_1('#skF_6', A_291)!='#skF_6' | ~r2_hidden(A_291, '#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1188, c_1736])).
% 5.10/1.97  tff(c_1748, plain, (![A_291]: (~r2_hidden(A_291, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_278, c_1639, c_1742])).
% 5.10/1.97  tff(c_1876, plain, (![A_322, B_323, C_324]: (k2_relset_1(A_322, B_323, C_324)=k2_relat_1(C_324) | ~m1_subset_1(C_324, k1_zfmisc_1(k2_zfmisc_1(A_322, B_323))))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.10/1.97  tff(c_1880, plain, (![A_322, B_323]: (k2_relset_1(A_322, B_323, '#skF_6')=k2_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_1184, c_1876])).
% 5.10/1.97  tff(c_1896, plain, (![A_322, B_323]: (k2_relset_1(A_322, B_323, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1197, c_1880])).
% 5.10/1.97  tff(c_88, plain, (![D_60, C_59, A_57, B_58]: (r2_hidden(k1_funct_1(D_60, C_59), k2_relset_1(A_57, B_58, D_60)) | k1_xboole_0=B_58 | ~r2_hidden(C_59, A_57) | ~m1_subset_1(D_60, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))) | ~v1_funct_2(D_60, A_57, B_58) | ~v1_funct_1(D_60))), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.10/1.97  tff(c_4111, plain, (![D_7890, C_7891, A_7892, B_7893]: (r2_hidden(k1_funct_1(D_7890, C_7891), k2_relset_1(A_7892, B_7893, D_7890)) | B_7893='#skF_6' | ~r2_hidden(C_7891, A_7892) | ~m1_subset_1(D_7890, k1_zfmisc_1(k2_zfmisc_1(A_7892, B_7893))) | ~v1_funct_2(D_7890, A_7892, B_7893) | ~v1_funct_1(D_7890))), inference(demodulation, [status(thm), theory('equality')], [c_1129, c_88])).
% 5.10/1.97  tff(c_4126, plain, (![C_7891, B_323, A_322]: (r2_hidden(k1_funct_1('#skF_6', C_7891), '#skF_6') | B_323='#skF_6' | ~r2_hidden(C_7891, A_322) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_322, B_323))) | ~v1_funct_2('#skF_6', A_322, B_323) | ~v1_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1896, c_4111])).
% 5.10/1.97  tff(c_4134, plain, (![C_7891, B_323, A_322]: (r2_hidden(k1_funct_1('#skF_6', C_7891), '#skF_6') | B_323='#skF_6' | ~r2_hidden(C_7891, A_322) | ~v1_funct_2('#skF_6', A_322, B_323))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_1184, c_4126])).
% 5.10/1.97  tff(c_4138, plain, (![B_7958, C_7959, A_7960]: (B_7958='#skF_6' | ~r2_hidden(C_7959, A_7960) | ~v1_funct_2('#skF_6', A_7960, B_7958))), inference(negUnitSimplification, [status(thm)], [c_1748, c_4134])).
% 5.10/1.97  tff(c_4157, plain, (![B_8025, A_8026]: (B_8025='#skF_6' | ~v1_funct_2('#skF_6', k1_tarski(A_8026), B_8025))), inference(resolution, [status(thm)], [c_157, c_4138])).
% 5.10/1.97  tff(c_4164, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_96, c_4157])).
% 5.10/1.97  tff(c_4168, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1189, c_4164])).
% 5.10/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.10/1.97  
% 5.10/1.97  Inference rules
% 5.10/1.97  ----------------------
% 5.10/1.97  #Ref     : 0
% 5.10/1.97  #Sup     : 656
% 5.10/1.97  #Fact    : 6
% 5.10/1.97  #Define  : 0
% 5.10/1.97  #Split   : 6
% 5.10/1.97  #Chain   : 0
% 5.10/1.97  #Close   : 0
% 5.10/1.97  
% 5.10/1.97  Ordering : KBO
% 5.10/1.97  
% 5.10/1.97  Simplification rules
% 5.10/1.97  ----------------------
% 5.10/1.97  #Subsume      : 109
% 5.10/1.97  #Demod        : 378
% 5.10/1.97  #Tautology    : 265
% 5.10/1.97  #SimpNegUnit  : 34
% 5.10/1.97  #BackRed      : 46
% 5.10/1.97  
% 5.10/1.97  #Partial instantiations: 4760
% 5.10/1.97  #Strategies tried      : 1
% 5.10/1.97  
% 5.10/1.97  Timing (in seconds)
% 5.10/1.97  ----------------------
% 5.10/1.97  Preprocessing        : 0.36
% 5.10/1.97  Parsing              : 0.19
% 5.10/1.97  CNF conversion       : 0.03
% 5.10/1.97  Main loop            : 0.84
% 5.10/1.97  Inferencing          : 0.37
% 5.10/1.97  Reduction            : 0.24
% 5.10/1.97  Demodulation         : 0.17
% 5.10/1.97  BG Simplification    : 0.03
% 5.10/1.97  Subsumption          : 0.13
% 5.10/1.97  Abstraction          : 0.03
% 5.10/1.97  MUC search           : 0.00
% 5.10/1.97  Cooper               : 0.00
% 5.10/1.97  Total                : 1.24
% 5.10/1.97  Index Insertion      : 0.00
% 5.10/1.97  Index Deletion       : 0.00
% 5.10/1.97  Index Matching       : 0.00
% 5.10/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
