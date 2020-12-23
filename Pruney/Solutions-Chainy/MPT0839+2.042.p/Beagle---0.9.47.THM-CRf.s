%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:27 EST 2020

% Result     : Theorem 4.07s
% Output     : CNFRefutation 4.29s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 150 expanded)
%              Number of leaves         :   42 (  68 expanded)
%              Depth                    :   13
%              Number of atoms          :  117 ( 267 expanded)
%              Number of equality atoms :   28 (  70 expanded)
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
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ~ ( k2_relset_1(B,A,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k1_relset_1(B,A,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relset_1)).

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
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

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
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

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

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_60,plain,(
    k2_relset_1('#skF_8','#skF_7','#skF_9') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_38,plain,(
    ! [A_36,B_37] : v1_relat_1(k2_zfmisc_1(A_36,B_37)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_62,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_101,plain,(
    ! [B_79,A_80] :
      ( v1_relat_1(B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(A_80))
      | ~ v1_relat_1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_107,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_8','#skF_7')) ),
    inference(resolution,[status(thm)],[c_62,c_101])).

tff(c_111,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_107])).

tff(c_152,plain,(
    ! [C_84,A_85,B_86] :
      ( v4_relat_1(C_84,A_85)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_161,plain,(
    v4_relat_1('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_62,c_152])).

tff(c_24,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k1_relat_1(B_16),A_15)
      | ~ v4_relat_1(B_16,A_15)
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

tff(c_42,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_763,plain,(
    ! [A_189,B_190] :
      ( r2_hidden(k4_tarski('#skF_3'(A_189,B_190),'#skF_4'(A_189,B_190)),A_189)
      | r2_hidden('#skF_5'(A_189,B_190),B_190)
      | k1_relat_1(A_189) = B_190 ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_375,plain,(
    ! [C_150,A_151] :
      ( r2_hidden(k4_tarski(C_150,'#skF_6'(A_151,k1_relat_1(A_151),C_150)),A_151)
      | ~ r2_hidden(C_150,k1_relat_1(A_151)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_397,plain,(
    ! [C_150] :
      ( r2_hidden(k4_tarski(C_150,'#skF_6'(k1_xboole_0,k1_xboole_0,C_150)),k1_xboole_0)
      | ~ r2_hidden(C_150,k1_relat_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_375])).

tff(c_405,plain,(
    ! [C_152] :
      ( r2_hidden(k4_tarski(C_152,'#skF_6'(k1_xboole_0,k1_xboole_0,C_152)),k1_xboole_0)
      | ~ r2_hidden(C_152,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_397])).

tff(c_48,plain,(
    ! [B_40,A_39] :
      ( ~ r1_tarski(B_40,A_39)
      | ~ r2_hidden(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_413,plain,(
    ! [C_152] :
      ( ~ r1_tarski(k1_xboole_0,k4_tarski(C_152,'#skF_6'(k1_xboole_0,k1_xboole_0,C_152)))
      | ~ r2_hidden(C_152,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_405,c_48])).

tff(c_424,plain,(
    ! [C_152] : ~ r2_hidden(C_152,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_413])).

tff(c_767,plain,(
    ! [B_190] :
      ( r2_hidden('#skF_5'(k1_xboole_0,B_190),B_190)
      | k1_relat_1(k1_xboole_0) = B_190 ) ),
    inference(resolution,[status(thm)],[c_763,c_424])).

tff(c_795,plain,(
    ! [B_191] :
      ( r2_hidden('#skF_5'(k1_xboole_0,B_191),B_191)
      | k1_xboole_0 = B_191 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_767])).

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

tff(c_892,plain,(
    ! [B_195,A_196] :
      ( m1_subset_1('#skF_5'(k1_xboole_0,B_195),A_196)
      | ~ r1_tarski(B_195,A_196)
      | k1_xboole_0 = B_195 ) ),
    inference(resolution,[status(thm)],[c_795,c_228])).

tff(c_311,plain,(
    ! [A_138,B_139,C_140] :
      ( k1_relset_1(A_138,B_139,C_140) = k1_relat_1(C_140)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_320,plain,(
    k1_relset_1('#skF_8','#skF_7','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_62,c_311])).

tff(c_58,plain,(
    ! [D_61] :
      ( ~ r2_hidden(D_61,k1_relset_1('#skF_8','#skF_7','#skF_9'))
      | ~ m1_subset_1(D_61,'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_343,plain,(
    ! [D_61] :
      ( ~ r2_hidden(D_61,k1_relat_1('#skF_9'))
      | ~ m1_subset_1(D_61,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_58])).

tff(c_803,plain,
    ( ~ m1_subset_1('#skF_5'(k1_xboole_0,k1_relat_1('#skF_9')),'#skF_8')
    | k1_relat_1('#skF_9') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_795,c_343])).

tff(c_820,plain,(
    ~ m1_subset_1('#skF_5'(k1_xboole_0,k1_relat_1('#skF_9')),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_803])).

tff(c_895,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_9'),'#skF_8')
    | k1_relat_1('#skF_9') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_892,c_820])).

tff(c_921,plain,(
    ~ r1_tarski(k1_relat_1('#skF_9'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_895])).

tff(c_930,plain,
    ( ~ v4_relat_1('#skF_9','#skF_8')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_24,c_921])).

tff(c_934,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_161,c_930])).

tff(c_935,plain,(
    k2_relat_1('#skF_9') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_115])).

tff(c_1074,plain,(
    ! [A_226,B_227,C_228] :
      ( k2_relset_1(A_226,B_227,C_228) = k2_relat_1(C_228)
      | ~ m1_subset_1(C_228,k1_zfmisc_1(k2_zfmisc_1(A_226,B_227))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1081,plain,(
    k2_relset_1('#skF_8','#skF_7','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_62,c_1074])).

tff(c_1084,plain,(
    k2_relset_1('#skF_8','#skF_7','#skF_9') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_935,c_1081])).

tff(c_1086,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1084])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:58:56 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.07/2.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.07/2.10  
% 4.07/2.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.07/2.11  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 4.07/2.11  
% 4.07/2.11  %Foreground sorts:
% 4.07/2.11  
% 4.07/2.11  
% 4.07/2.11  %Background operators:
% 4.07/2.11  
% 4.07/2.11  
% 4.07/2.11  %Foreground operators:
% 4.07/2.11  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.07/2.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.07/2.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.07/2.11  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 4.07/2.11  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.07/2.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.07/2.11  tff('#skF_7', type, '#skF_7': $i).
% 4.07/2.11  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.07/2.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.07/2.11  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.07/2.11  tff('#skF_9', type, '#skF_9': $i).
% 4.07/2.11  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.07/2.11  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.07/2.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.07/2.11  tff('#skF_8', type, '#skF_8': $i).
% 4.07/2.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.07/2.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.07/2.11  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.07/2.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.07/2.11  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.07/2.11  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.07/2.11  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.07/2.11  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.07/2.11  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.07/2.11  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.07/2.11  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.07/2.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.07/2.11  
% 4.29/2.13  tff(f_116, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_relset_1)).
% 4.29/2.13  tff(f_67, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.29/2.13  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.29/2.13  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.29/2.13  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 4.29/2.13  tff(f_76, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 4.29/2.13  tff(f_70, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 4.29/2.13  tff(f_65, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 4.29/2.13  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.29/2.13  tff(f_81, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.29/2.13  tff(f_34, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 4.29/2.13  tff(f_38, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 4.29/2.13  tff(f_44, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 4.29/2.13  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.29/2.13  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.29/2.13  tff(c_60, plain, (k2_relset_1('#skF_8', '#skF_7', '#skF_9')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.29/2.13  tff(c_38, plain, (![A_36, B_37]: (v1_relat_1(k2_zfmisc_1(A_36, B_37)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.29/2.13  tff(c_62, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.29/2.13  tff(c_101, plain, (![B_79, A_80]: (v1_relat_1(B_79) | ~m1_subset_1(B_79, k1_zfmisc_1(A_80)) | ~v1_relat_1(A_80))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.29/2.13  tff(c_107, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_8', '#skF_7'))), inference(resolution, [status(thm)], [c_62, c_101])).
% 4.29/2.13  tff(c_111, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_107])).
% 4.29/2.13  tff(c_152, plain, (![C_84, A_85, B_86]: (v4_relat_1(C_84, A_85) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.29/2.13  tff(c_161, plain, (v4_relat_1('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_62, c_152])).
% 4.29/2.13  tff(c_24, plain, (![B_16, A_15]: (r1_tarski(k1_relat_1(B_16), A_15) | ~v4_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.29/2.13  tff(c_46, plain, (![A_38]: (k2_relat_1(A_38)=k1_xboole_0 | k1_relat_1(A_38)!=k1_xboole_0 | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.29/2.13  tff(c_115, plain, (k2_relat_1('#skF_9')=k1_xboole_0 | k1_relat_1('#skF_9')!=k1_xboole_0), inference(resolution, [status(thm)], [c_111, c_46])).
% 4.29/2.13  tff(c_116, plain, (k1_relat_1('#skF_9')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_115])).
% 4.29/2.13  tff(c_42, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.29/2.13  tff(c_763, plain, (![A_189, B_190]: (r2_hidden(k4_tarski('#skF_3'(A_189, B_190), '#skF_4'(A_189, B_190)), A_189) | r2_hidden('#skF_5'(A_189, B_190), B_190) | k1_relat_1(A_189)=B_190)), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.29/2.13  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.29/2.13  tff(c_375, plain, (![C_150, A_151]: (r2_hidden(k4_tarski(C_150, '#skF_6'(A_151, k1_relat_1(A_151), C_150)), A_151) | ~r2_hidden(C_150, k1_relat_1(A_151)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.29/2.13  tff(c_397, plain, (![C_150]: (r2_hidden(k4_tarski(C_150, '#skF_6'(k1_xboole_0, k1_xboole_0, C_150)), k1_xboole_0) | ~r2_hidden(C_150, k1_relat_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_375])).
% 4.29/2.13  tff(c_405, plain, (![C_152]: (r2_hidden(k4_tarski(C_152, '#skF_6'(k1_xboole_0, k1_xboole_0, C_152)), k1_xboole_0) | ~r2_hidden(C_152, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_397])).
% 4.29/2.13  tff(c_48, plain, (![B_40, A_39]: (~r1_tarski(B_40, A_39) | ~r2_hidden(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.29/2.13  tff(c_413, plain, (![C_152]: (~r1_tarski(k1_xboole_0, k4_tarski(C_152, '#skF_6'(k1_xboole_0, k1_xboole_0, C_152))) | ~r2_hidden(C_152, k1_xboole_0))), inference(resolution, [status(thm)], [c_405, c_48])).
% 4.29/2.13  tff(c_424, plain, (![C_152]: (~r2_hidden(C_152, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_413])).
% 4.29/2.13  tff(c_767, plain, (![B_190]: (r2_hidden('#skF_5'(k1_xboole_0, B_190), B_190) | k1_relat_1(k1_xboole_0)=B_190)), inference(resolution, [status(thm)], [c_763, c_424])).
% 4.29/2.13  tff(c_795, plain, (![B_191]: (r2_hidden('#skF_5'(k1_xboole_0, B_191), B_191) | k1_xboole_0=B_191)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_767])).
% 4.29/2.13  tff(c_80, plain, (![C_70, A_71]: (r2_hidden(C_70, k1_zfmisc_1(A_71)) | ~r1_tarski(C_70, A_71))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.29/2.13  tff(c_16, plain, (![A_7, B_8]: (m1_subset_1(A_7, B_8) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.29/2.13  tff(c_88, plain, (![C_70, A_71]: (m1_subset_1(C_70, k1_zfmisc_1(A_71)) | ~r1_tarski(C_70, A_71))), inference(resolution, [status(thm)], [c_80, c_16])).
% 4.29/2.13  tff(c_223, plain, (![A_105, C_106, B_107]: (m1_subset_1(A_105, C_106) | ~m1_subset_1(B_107, k1_zfmisc_1(C_106)) | ~r2_hidden(A_105, B_107))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.29/2.13  tff(c_228, plain, (![A_105, A_71, C_70]: (m1_subset_1(A_105, A_71) | ~r2_hidden(A_105, C_70) | ~r1_tarski(C_70, A_71))), inference(resolution, [status(thm)], [c_88, c_223])).
% 4.29/2.13  tff(c_892, plain, (![B_195, A_196]: (m1_subset_1('#skF_5'(k1_xboole_0, B_195), A_196) | ~r1_tarski(B_195, A_196) | k1_xboole_0=B_195)), inference(resolution, [status(thm)], [c_795, c_228])).
% 4.29/2.13  tff(c_311, plain, (![A_138, B_139, C_140]: (k1_relset_1(A_138, B_139, C_140)=k1_relat_1(C_140) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.29/2.13  tff(c_320, plain, (k1_relset_1('#skF_8', '#skF_7', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_62, c_311])).
% 4.29/2.13  tff(c_58, plain, (![D_61]: (~r2_hidden(D_61, k1_relset_1('#skF_8', '#skF_7', '#skF_9')) | ~m1_subset_1(D_61, '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.29/2.13  tff(c_343, plain, (![D_61]: (~r2_hidden(D_61, k1_relat_1('#skF_9')) | ~m1_subset_1(D_61, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_320, c_58])).
% 4.29/2.13  tff(c_803, plain, (~m1_subset_1('#skF_5'(k1_xboole_0, k1_relat_1('#skF_9')), '#skF_8') | k1_relat_1('#skF_9')=k1_xboole_0), inference(resolution, [status(thm)], [c_795, c_343])).
% 4.29/2.13  tff(c_820, plain, (~m1_subset_1('#skF_5'(k1_xboole_0, k1_relat_1('#skF_9')), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_116, c_803])).
% 4.29/2.13  tff(c_895, plain, (~r1_tarski(k1_relat_1('#skF_9'), '#skF_8') | k1_relat_1('#skF_9')=k1_xboole_0), inference(resolution, [status(thm)], [c_892, c_820])).
% 4.29/2.13  tff(c_921, plain, (~r1_tarski(k1_relat_1('#skF_9'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_116, c_895])).
% 4.29/2.13  tff(c_930, plain, (~v4_relat_1('#skF_9', '#skF_8') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_24, c_921])).
% 4.29/2.13  tff(c_934, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_111, c_161, c_930])).
% 4.29/2.13  tff(c_935, plain, (k2_relat_1('#skF_9')=k1_xboole_0), inference(splitRight, [status(thm)], [c_115])).
% 4.29/2.13  tff(c_1074, plain, (![A_226, B_227, C_228]: (k2_relset_1(A_226, B_227, C_228)=k2_relat_1(C_228) | ~m1_subset_1(C_228, k1_zfmisc_1(k2_zfmisc_1(A_226, B_227))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.29/2.13  tff(c_1081, plain, (k2_relset_1('#skF_8', '#skF_7', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_62, c_1074])).
% 4.29/2.13  tff(c_1084, plain, (k2_relset_1('#skF_8', '#skF_7', '#skF_9')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_935, c_1081])).
% 4.29/2.13  tff(c_1086, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_1084])).
% 4.29/2.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.29/2.13  
% 4.29/2.13  Inference rules
% 4.29/2.13  ----------------------
% 4.29/2.13  #Ref     : 0
% 4.29/2.13  #Sup     : 202
% 4.29/2.13  #Fact    : 0
% 4.29/2.13  #Define  : 0
% 4.29/2.13  #Split   : 4
% 4.29/2.13  #Chain   : 0
% 4.29/2.13  #Close   : 0
% 4.29/2.13  
% 4.29/2.13  Ordering : KBO
% 4.29/2.13  
% 4.29/2.13  Simplification rules
% 4.29/2.13  ----------------------
% 4.29/2.13  #Subsume      : 20
% 4.29/2.13  #Demod        : 60
% 4.29/2.13  #Tautology    : 40
% 4.29/2.13  #SimpNegUnit  : 13
% 4.29/2.13  #BackRed      : 6
% 4.29/2.13  
% 4.29/2.13  #Partial instantiations: 0
% 4.29/2.13  #Strategies tried      : 1
% 4.29/2.13  
% 4.29/2.13  Timing (in seconds)
% 4.29/2.13  ----------------------
% 4.29/2.14  Preprocessing        : 0.53
% 4.29/2.14  Parsing              : 0.26
% 4.29/2.14  CNF conversion       : 0.05
% 4.29/2.14  Main loop            : 0.70
% 4.29/2.14  Inferencing          : 0.27
% 4.29/2.14  Reduction            : 0.20
% 4.29/2.14  Demodulation         : 0.14
% 4.29/2.14  BG Simplification    : 0.04
% 4.29/2.14  Subsumption          : 0.13
% 4.29/2.14  Abstraction          : 0.04
% 4.29/2.14  MUC search           : 0.00
% 4.29/2.14  Cooper               : 0.00
% 4.29/2.14  Total                : 1.29
% 4.29/2.14  Index Insertion      : 0.00
% 4.29/2.14  Index Deletion       : 0.00
% 4.29/2.14  Index Matching       : 0.00
% 4.29/2.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
