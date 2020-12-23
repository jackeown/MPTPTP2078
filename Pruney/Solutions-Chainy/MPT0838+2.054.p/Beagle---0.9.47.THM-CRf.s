%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:16 EST 2020

% Result     : Theorem 3.27s
% Output     : CNFRefutation 3.41s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 174 expanded)
%              Number of leaves         :   42 (  76 expanded)
%              Depth                    :   13
%              Number of atoms          :  123 ( 321 expanded)
%              Number of equality atoms :   33 (  86 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

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

tff(f_116,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ~ ( k1_relset_1(A,B,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k2_relset_1(A,B,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relset_1)).

tff(f_67,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_70,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_60,plain,(
    k1_relset_1('#skF_7','#skF_8','#skF_9') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_38,plain,(
    ! [A_36,B_37] : v1_relat_1(k2_zfmisc_1(A_36,B_37)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_62,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_101,plain,(
    ! [B_79,A_80] :
      ( v1_relat_1(B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(A_80))
      | ~ v1_relat_1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_107,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_62,c_101])).

tff(c_111,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_107])).

tff(c_176,plain,(
    ! [C_94,B_95,A_96] :
      ( v5_relat_1(C_94,B_95)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_96,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_185,plain,(
    v5_relat_1('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_62,c_176])).

tff(c_24,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k2_relat_1(B_16),A_15)
      | ~ v5_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_46,plain,(
    ! [A_38] :
      ( k2_relat_1(A_38) = k1_xboole_0
      | k1_relat_1(A_38) != k1_xboole_0
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_115,plain,
    ( k2_relat_1('#skF_9') = k1_xboole_0
    | k1_relat_1('#skF_9') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_111,c_46])).

tff(c_116,plain,(
    k1_relat_1('#skF_9') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_115])).

tff(c_135,plain,(
    ! [A_83] :
      ( k1_relat_1(A_83) = k1_xboole_0
      | k2_relat_1(A_83) != k1_xboole_0
      | ~ v1_relat_1(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_141,plain,
    ( k1_relat_1('#skF_9') = k1_xboole_0
    | k2_relat_1('#skF_9') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_111,c_135])).

tff(c_150,plain,(
    k2_relat_1('#skF_9') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_141])).

tff(c_40,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_740,plain,(
    ! [A_191,B_192] :
      ( r2_hidden(k4_tarski('#skF_4'(A_191,B_192),'#skF_3'(A_191,B_192)),A_191)
      | r2_hidden('#skF_5'(A_191,B_192),B_192)
      | k2_relat_1(A_191) = B_192 ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_359,plain,(
    ! [A_148,C_149] :
      ( r2_hidden(k4_tarski('#skF_6'(A_148,k2_relat_1(A_148),C_149),C_149),A_148)
      | ~ r2_hidden(C_149,k2_relat_1(A_148)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_384,plain,(
    ! [C_149] :
      ( r2_hidden(k4_tarski('#skF_6'(k1_xboole_0,k1_xboole_0,C_149),C_149),k1_xboole_0)
      | ~ r2_hidden(C_149,k2_relat_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_359])).

tff(c_392,plain,(
    ! [C_150] :
      ( r2_hidden(k4_tarski('#skF_6'(k1_xboole_0,k1_xboole_0,C_150),C_150),k1_xboole_0)
      | ~ r2_hidden(C_150,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_384])).

tff(c_48,plain,(
    ! [B_40,A_39] :
      ( ~ r1_tarski(B_40,A_39)
      | ~ r2_hidden(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_400,plain,(
    ! [C_150] :
      ( ~ r1_tarski(k1_xboole_0,k4_tarski('#skF_6'(k1_xboole_0,k1_xboole_0,C_150),C_150))
      | ~ r2_hidden(C_150,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_392,c_48])).

tff(c_411,plain,(
    ! [C_150] : ~ r2_hidden(C_150,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_400])).

tff(c_744,plain,(
    ! [B_192] :
      ( r2_hidden('#skF_5'(k1_xboole_0,B_192),B_192)
      | k2_relat_1(k1_xboole_0) = B_192 ) ),
    inference(resolution,[status(thm)],[c_740,c_411])).

tff(c_772,plain,(
    ! [B_193] :
      ( r2_hidden('#skF_5'(k1_xboole_0,B_193),B_193)
      | k1_xboole_0 = B_193 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_744])).

tff(c_80,plain,(
    ! [C_70,A_71] :
      ( r2_hidden(C_70,k1_zfmisc_1(A_71))
      | ~ r1_tarski(C_70,A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_16,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,B_8)
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_88,plain,(
    ! [C_70,A_71] :
      ( m1_subset_1(C_70,k1_zfmisc_1(A_71))
      | ~ r1_tarski(C_70,A_71) ) ),
    inference(resolution,[status(thm)],[c_80,c_16])).

tff(c_223,plain,(
    ! [A_105,C_106,B_107] :
      ( m1_subset_1(A_105,C_106)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(C_106))
      | ~ r2_hidden(A_105,B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_228,plain,(
    ! [A_105,A_71,C_70] :
      ( m1_subset_1(A_105,A_71)
      | ~ r2_hidden(A_105,C_70)
      | ~ r1_tarski(C_70,A_71) ) ),
    inference(resolution,[status(thm)],[c_88,c_223])).

tff(c_870,plain,(
    ! [B_198,A_199] :
      ( m1_subset_1('#skF_5'(k1_xboole_0,B_198),A_199)
      | ~ r1_tarski(B_198,A_199)
      | k1_xboole_0 = B_198 ) ),
    inference(resolution,[status(thm)],[c_772,c_228])).

tff(c_231,plain,(
    ! [A_109,B_110,C_111] :
      ( k2_relset_1(A_109,B_110,C_111) = k2_relat_1(C_111)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_240,plain,(
    k2_relset_1('#skF_7','#skF_8','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_62,c_231])).

tff(c_58,plain,(
    ! [D_61] :
      ( ~ r2_hidden(D_61,k2_relset_1('#skF_7','#skF_8','#skF_9'))
      | ~ m1_subset_1(D_61,'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_241,plain,(
    ! [D_61] :
      ( ~ r2_hidden(D_61,k2_relat_1('#skF_9'))
      | ~ m1_subset_1(D_61,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_58])).

tff(c_782,plain,
    ( ~ m1_subset_1('#skF_5'(k1_xboole_0,k2_relat_1('#skF_9')),'#skF_8')
    | k2_relat_1('#skF_9') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_772,c_241])).

tff(c_798,plain,(
    ~ m1_subset_1('#skF_5'(k1_xboole_0,k2_relat_1('#skF_9')),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_150,c_782])).

tff(c_873,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_9'),'#skF_8')
    | k2_relat_1('#skF_9') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_870,c_798])).

tff(c_899,plain,(
    ~ r1_tarski(k2_relat_1('#skF_9'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_150,c_873])).

tff(c_908,plain,
    ( ~ v5_relat_1('#skF_9','#skF_8')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_24,c_899])).

tff(c_912,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_185,c_908])).

tff(c_914,plain,(
    k1_relat_1('#skF_9') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_115])).

tff(c_1073,plain,(
    ! [A_236,B_237,C_238] :
      ( k1_relset_1(A_236,B_237,C_238) = k1_relat_1(C_238)
      | ~ m1_subset_1(C_238,k1_zfmisc_1(k2_zfmisc_1(A_236,B_237))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1080,plain,(
    k1_relset_1('#skF_7','#skF_8','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_62,c_1073])).

tff(c_1083,plain,(
    k1_relset_1('#skF_7','#skF_8','#skF_9') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_914,c_1080])).

tff(c_1085,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1083])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:42:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.27/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.41/1.56  
% 3.41/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.41/1.57  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 3.41/1.57  
% 3.41/1.57  %Foreground sorts:
% 3.41/1.57  
% 3.41/1.57  
% 3.41/1.57  %Background operators:
% 3.41/1.57  
% 3.41/1.57  
% 3.41/1.57  %Foreground operators:
% 3.41/1.57  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.41/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.41/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.41/1.57  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.41/1.57  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.41/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.41/1.57  tff('#skF_7', type, '#skF_7': $i).
% 3.41/1.57  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.41/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.41/1.57  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.41/1.57  tff('#skF_9', type, '#skF_9': $i).
% 3.41/1.57  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.41/1.57  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.41/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.41/1.57  tff('#skF_8', type, '#skF_8': $i).
% 3.41/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.41/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.41/1.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.41/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.41/1.57  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.41/1.57  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.41/1.57  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.41/1.57  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.41/1.57  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.41/1.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.41/1.57  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.41/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.41/1.57  
% 3.41/1.58  tff(f_116, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_relset_1)).
% 3.41/1.58  tff(f_67, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.41/1.58  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.41/1.58  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.41/1.58  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.41/1.58  tff(f_76, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 3.41/1.58  tff(f_70, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.41/1.58  tff(f_65, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 3.41/1.58  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.41/1.58  tff(f_81, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.41/1.58  tff(f_34, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.41/1.58  tff(f_38, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 3.41/1.58  tff(f_44, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.41/1.58  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.41/1.58  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.41/1.58  tff(c_60, plain, (k1_relset_1('#skF_7', '#skF_8', '#skF_9')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.41/1.58  tff(c_38, plain, (![A_36, B_37]: (v1_relat_1(k2_zfmisc_1(A_36, B_37)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.41/1.58  tff(c_62, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.41/1.58  tff(c_101, plain, (![B_79, A_80]: (v1_relat_1(B_79) | ~m1_subset_1(B_79, k1_zfmisc_1(A_80)) | ~v1_relat_1(A_80))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.41/1.58  tff(c_107, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_62, c_101])).
% 3.41/1.58  tff(c_111, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_107])).
% 3.41/1.58  tff(c_176, plain, (![C_94, B_95, A_96]: (v5_relat_1(C_94, B_95) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_96, B_95))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.41/1.58  tff(c_185, plain, (v5_relat_1('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_62, c_176])).
% 3.41/1.58  tff(c_24, plain, (![B_16, A_15]: (r1_tarski(k2_relat_1(B_16), A_15) | ~v5_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.41/1.58  tff(c_46, plain, (![A_38]: (k2_relat_1(A_38)=k1_xboole_0 | k1_relat_1(A_38)!=k1_xboole_0 | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.41/1.58  tff(c_115, plain, (k2_relat_1('#skF_9')=k1_xboole_0 | k1_relat_1('#skF_9')!=k1_xboole_0), inference(resolution, [status(thm)], [c_111, c_46])).
% 3.41/1.58  tff(c_116, plain, (k1_relat_1('#skF_9')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_115])).
% 3.41/1.58  tff(c_135, plain, (![A_83]: (k1_relat_1(A_83)=k1_xboole_0 | k2_relat_1(A_83)!=k1_xboole_0 | ~v1_relat_1(A_83))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.41/1.58  tff(c_141, plain, (k1_relat_1('#skF_9')=k1_xboole_0 | k2_relat_1('#skF_9')!=k1_xboole_0), inference(resolution, [status(thm)], [c_111, c_135])).
% 3.41/1.58  tff(c_150, plain, (k2_relat_1('#skF_9')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_116, c_141])).
% 3.41/1.58  tff(c_40, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.41/1.58  tff(c_740, plain, (![A_191, B_192]: (r2_hidden(k4_tarski('#skF_4'(A_191, B_192), '#skF_3'(A_191, B_192)), A_191) | r2_hidden('#skF_5'(A_191, B_192), B_192) | k2_relat_1(A_191)=B_192)), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.41/1.58  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.41/1.58  tff(c_359, plain, (![A_148, C_149]: (r2_hidden(k4_tarski('#skF_6'(A_148, k2_relat_1(A_148), C_149), C_149), A_148) | ~r2_hidden(C_149, k2_relat_1(A_148)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.41/1.58  tff(c_384, plain, (![C_149]: (r2_hidden(k4_tarski('#skF_6'(k1_xboole_0, k1_xboole_0, C_149), C_149), k1_xboole_0) | ~r2_hidden(C_149, k2_relat_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_359])).
% 3.41/1.58  tff(c_392, plain, (![C_150]: (r2_hidden(k4_tarski('#skF_6'(k1_xboole_0, k1_xboole_0, C_150), C_150), k1_xboole_0) | ~r2_hidden(C_150, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_384])).
% 3.41/1.58  tff(c_48, plain, (![B_40, A_39]: (~r1_tarski(B_40, A_39) | ~r2_hidden(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.41/1.58  tff(c_400, plain, (![C_150]: (~r1_tarski(k1_xboole_0, k4_tarski('#skF_6'(k1_xboole_0, k1_xboole_0, C_150), C_150)) | ~r2_hidden(C_150, k1_xboole_0))), inference(resolution, [status(thm)], [c_392, c_48])).
% 3.41/1.58  tff(c_411, plain, (![C_150]: (~r2_hidden(C_150, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_400])).
% 3.41/1.58  tff(c_744, plain, (![B_192]: (r2_hidden('#skF_5'(k1_xboole_0, B_192), B_192) | k2_relat_1(k1_xboole_0)=B_192)), inference(resolution, [status(thm)], [c_740, c_411])).
% 3.41/1.58  tff(c_772, plain, (![B_193]: (r2_hidden('#skF_5'(k1_xboole_0, B_193), B_193) | k1_xboole_0=B_193)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_744])).
% 3.41/1.58  tff(c_80, plain, (![C_70, A_71]: (r2_hidden(C_70, k1_zfmisc_1(A_71)) | ~r1_tarski(C_70, A_71))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.41/1.58  tff(c_16, plain, (![A_7, B_8]: (m1_subset_1(A_7, B_8) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.41/1.58  tff(c_88, plain, (![C_70, A_71]: (m1_subset_1(C_70, k1_zfmisc_1(A_71)) | ~r1_tarski(C_70, A_71))), inference(resolution, [status(thm)], [c_80, c_16])).
% 3.41/1.58  tff(c_223, plain, (![A_105, C_106, B_107]: (m1_subset_1(A_105, C_106) | ~m1_subset_1(B_107, k1_zfmisc_1(C_106)) | ~r2_hidden(A_105, B_107))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.41/1.58  tff(c_228, plain, (![A_105, A_71, C_70]: (m1_subset_1(A_105, A_71) | ~r2_hidden(A_105, C_70) | ~r1_tarski(C_70, A_71))), inference(resolution, [status(thm)], [c_88, c_223])).
% 3.41/1.58  tff(c_870, plain, (![B_198, A_199]: (m1_subset_1('#skF_5'(k1_xboole_0, B_198), A_199) | ~r1_tarski(B_198, A_199) | k1_xboole_0=B_198)), inference(resolution, [status(thm)], [c_772, c_228])).
% 3.41/1.58  tff(c_231, plain, (![A_109, B_110, C_111]: (k2_relset_1(A_109, B_110, C_111)=k2_relat_1(C_111) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.41/1.58  tff(c_240, plain, (k2_relset_1('#skF_7', '#skF_8', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_62, c_231])).
% 3.41/1.58  tff(c_58, plain, (![D_61]: (~r2_hidden(D_61, k2_relset_1('#skF_7', '#skF_8', '#skF_9')) | ~m1_subset_1(D_61, '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.41/1.58  tff(c_241, plain, (![D_61]: (~r2_hidden(D_61, k2_relat_1('#skF_9')) | ~m1_subset_1(D_61, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_240, c_58])).
% 3.41/1.58  tff(c_782, plain, (~m1_subset_1('#skF_5'(k1_xboole_0, k2_relat_1('#skF_9')), '#skF_8') | k2_relat_1('#skF_9')=k1_xboole_0), inference(resolution, [status(thm)], [c_772, c_241])).
% 3.41/1.58  tff(c_798, plain, (~m1_subset_1('#skF_5'(k1_xboole_0, k2_relat_1('#skF_9')), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_150, c_782])).
% 3.41/1.58  tff(c_873, plain, (~r1_tarski(k2_relat_1('#skF_9'), '#skF_8') | k2_relat_1('#skF_9')=k1_xboole_0), inference(resolution, [status(thm)], [c_870, c_798])).
% 3.41/1.58  tff(c_899, plain, (~r1_tarski(k2_relat_1('#skF_9'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_150, c_873])).
% 3.41/1.58  tff(c_908, plain, (~v5_relat_1('#skF_9', '#skF_8') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_24, c_899])).
% 3.41/1.58  tff(c_912, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_111, c_185, c_908])).
% 3.41/1.58  tff(c_914, plain, (k1_relat_1('#skF_9')=k1_xboole_0), inference(splitRight, [status(thm)], [c_115])).
% 3.41/1.58  tff(c_1073, plain, (![A_236, B_237, C_238]: (k1_relset_1(A_236, B_237, C_238)=k1_relat_1(C_238) | ~m1_subset_1(C_238, k1_zfmisc_1(k2_zfmisc_1(A_236, B_237))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.41/1.58  tff(c_1080, plain, (k1_relset_1('#skF_7', '#skF_8', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_62, c_1073])).
% 3.41/1.58  tff(c_1083, plain, (k1_relset_1('#skF_7', '#skF_8', '#skF_9')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_914, c_1080])).
% 3.41/1.58  tff(c_1085, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_1083])).
% 3.41/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.41/1.58  
% 3.41/1.58  Inference rules
% 3.41/1.58  ----------------------
% 3.41/1.58  #Ref     : 0
% 3.41/1.58  #Sup     : 201
% 3.41/1.58  #Fact    : 0
% 3.41/1.58  #Define  : 0
% 3.41/1.58  #Split   : 5
% 3.41/1.58  #Chain   : 0
% 3.41/1.58  #Close   : 0
% 3.41/1.58  
% 3.41/1.58  Ordering : KBO
% 3.41/1.58  
% 3.41/1.58  Simplification rules
% 3.41/1.58  ----------------------
% 3.41/1.58  #Subsume      : 27
% 3.41/1.58  #Demod        : 67
% 3.41/1.58  #Tautology    : 46
% 3.41/1.58  #SimpNegUnit  : 19
% 3.41/1.58  #BackRed      : 10
% 3.41/1.58  
% 3.41/1.58  #Partial instantiations: 0
% 3.41/1.58  #Strategies tried      : 1
% 3.41/1.58  
% 3.41/1.58  Timing (in seconds)
% 3.41/1.58  ----------------------
% 3.41/1.59  Preprocessing        : 0.36
% 3.41/1.59  Parsing              : 0.17
% 3.41/1.59  CNF conversion       : 0.03
% 3.41/1.59  Main loop            : 0.44
% 3.41/1.59  Inferencing          : 0.16
% 3.41/1.59  Reduction            : 0.13
% 3.41/1.59  Demodulation         : 0.09
% 3.41/1.59  BG Simplification    : 0.02
% 3.41/1.59  Subsumption          : 0.08
% 3.41/1.59  Abstraction          : 0.03
% 3.41/1.59  MUC search           : 0.00
% 3.41/1.59  Cooper               : 0.00
% 3.41/1.59  Total                : 0.84
% 3.41/1.59  Index Insertion      : 0.00
% 3.41/1.59  Index Deletion       : 0.00
% 3.41/1.59  Index Matching       : 0.00
% 3.41/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
