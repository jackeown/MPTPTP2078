%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:09 EST 2020

% Result     : Theorem 8.02s
% Output     : CNFRefutation 8.02s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 199 expanded)
%              Number of leaves         :   30 (  80 expanded)
%              Depth                    :   12
%              Number of atoms          :  106 ( 383 expanded)
%              Number of equality atoms :   30 ( 124 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k1_relset_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_11 > #skF_6 > #skF_7 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
        <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_44,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_46,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_128,plain,(
    ! [A_80,B_81,C_82] :
      ( k1_relset_1(A_80,B_81,C_82) = k1_relat_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_137,plain,(
    k1_relset_1('#skF_8','#skF_7','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_46,c_128])).

tff(c_52,plain,
    ( k1_relset_1('#skF_8','#skF_7','#skF_9') != '#skF_8'
    | r2_hidden('#skF_11','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_86,plain,(
    k1_relset_1('#skF_8','#skF_7','#skF_9') != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_138,plain,(
    k1_relat_1('#skF_9') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_86])).

tff(c_1918,plain,(
    ! [A_194,B_195] :
      ( r2_hidden(k4_tarski('#skF_3'(A_194,B_195),'#skF_4'(A_194,B_195)),A_194)
      | r2_hidden('#skF_5'(A_194,B_195),B_195)
      | k1_relat_1(A_194) = B_195 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_61,plain,(
    ! [A_51,B_52] :
      ( r1_tarski(A_51,B_52)
      | ~ m1_subset_1(A_51,k1_zfmisc_1(B_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_69,plain,(
    r1_tarski('#skF_9',k2_zfmisc_1('#skF_8','#skF_7')) ),
    inference(resolution,[status(thm)],[c_46,c_61])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_73,plain,(
    k3_xboole_0('#skF_9',k2_zfmisc_1('#skF_8','#skF_7')) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_69,c_20])).

tff(c_82,plain,(
    ! [D_56,B_57,A_58] :
      ( r2_hidden(D_56,B_57)
      | ~ r2_hidden(D_56,k3_xboole_0(A_58,B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_85,plain,(
    ! [D_56] :
      ( r2_hidden(D_56,k2_zfmisc_1('#skF_8','#skF_7'))
      | ~ r2_hidden(D_56,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_82])).

tff(c_95,plain,(
    ! [A_63,C_64,B_65,D_66] :
      ( r2_hidden(A_63,C_64)
      | ~ r2_hidden(k4_tarski(A_63,B_65),k2_zfmisc_1(C_64,D_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_100,plain,(
    ! [A_63,B_65] :
      ( r2_hidden(A_63,'#skF_8')
      | ~ r2_hidden(k4_tarski(A_63,B_65),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_85,c_95])).

tff(c_2040,plain,(
    ! [B_197] :
      ( r2_hidden('#skF_3'('#skF_9',B_197),'#skF_8')
      | r2_hidden('#skF_5'('#skF_9',B_197),B_197)
      | k1_relat_1('#skF_9') = B_197 ) ),
    inference(resolution,[status(thm)],[c_1918,c_100])).

tff(c_40,plain,(
    ! [A_15,B_16] :
      ( ~ r2_hidden('#skF_3'(A_15,B_16),B_16)
      | r2_hidden('#skF_5'(A_15,B_16),B_16)
      | k1_relat_1(A_15) = B_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2051,plain,
    ( r2_hidden('#skF_5'('#skF_9','#skF_8'),'#skF_8')
    | k1_relat_1('#skF_9') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_2040,c_40])).

tff(c_2081,plain,(
    r2_hidden('#skF_5'('#skF_9','#skF_8'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_138,c_138,c_2051])).

tff(c_58,plain,(
    ! [D_43] :
      ( r2_hidden(k4_tarski(D_43,'#skF_10'(D_43)),'#skF_9')
      | ~ r2_hidden(D_43,'#skF_8')
      | k1_relset_1('#skF_8','#skF_7','#skF_9') = '#skF_8' ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_205,plain,(
    ! [D_43] :
      ( r2_hidden(k4_tarski(D_43,'#skF_10'(D_43)),'#skF_9')
      | ~ r2_hidden(D_43,'#skF_8')
      | k1_relat_1('#skF_9') = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_58])).

tff(c_206,plain,(
    ! [D_43] :
      ( r2_hidden(k4_tarski(D_43,'#skF_10'(D_43)),'#skF_9')
      | ~ r2_hidden(D_43,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_138,c_205])).

tff(c_207,plain,(
    ! [D_91] :
      ( r2_hidden(k4_tarski(D_91,'#skF_10'(D_91)),'#skF_9')
      | ~ r2_hidden(D_91,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_138,c_205])).

tff(c_34,plain,(
    ! [C_30,A_15,D_33] :
      ( r2_hidden(C_30,k1_relat_1(A_15))
      | ~ r2_hidden(k4_tarski(C_30,D_33),A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_222,plain,(
    ! [D_91] :
      ( r2_hidden(D_91,k1_relat_1('#skF_9'))
      | ~ r2_hidden(D_91,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_207,c_34])).

tff(c_32,plain,(
    ! [C_30,A_15] :
      ( r2_hidden(k4_tarski(C_30,'#skF_6'(A_15,k1_relat_1(A_15),C_30)),A_15)
      | ~ r2_hidden(C_30,k1_relat_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2346,plain,(
    ! [A_209,B_210,D_211] :
      ( r2_hidden(k4_tarski('#skF_3'(A_209,B_210),'#skF_4'(A_209,B_210)),A_209)
      | ~ r2_hidden(k4_tarski('#skF_5'(A_209,B_210),D_211),A_209)
      | k1_relat_1(A_209) = B_210 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8638,plain,(
    ! [A_335,B_336] :
      ( r2_hidden(k4_tarski('#skF_3'(A_335,B_336),'#skF_4'(A_335,B_336)),A_335)
      | k1_relat_1(A_335) = B_336
      | ~ r2_hidden('#skF_5'(A_335,B_336),k1_relat_1(A_335)) ) ),
    inference(resolution,[status(thm)],[c_32,c_2346])).

tff(c_8965,plain,(
    ! [B_341] :
      ( r2_hidden('#skF_3'('#skF_9',B_341),'#skF_8')
      | k1_relat_1('#skF_9') = B_341
      | ~ r2_hidden('#skF_5'('#skF_9',B_341),k1_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_8638,c_100])).

tff(c_8984,plain,(
    ! [B_342] :
      ( r2_hidden('#skF_3'('#skF_9',B_342),'#skF_8')
      | k1_relat_1('#skF_9') = B_342
      | ~ r2_hidden('#skF_5'('#skF_9',B_342),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_222,c_8965])).

tff(c_36,plain,(
    ! [A_15,B_16,D_29] :
      ( ~ r2_hidden('#skF_3'(A_15,B_16),B_16)
      | ~ r2_hidden(k4_tarski('#skF_5'(A_15,B_16),D_29),A_15)
      | k1_relat_1(A_15) = B_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8993,plain,(
    ! [D_29] :
      ( ~ r2_hidden(k4_tarski('#skF_5'('#skF_9','#skF_8'),D_29),'#skF_9')
      | k1_relat_1('#skF_9') = '#skF_8'
      | ~ r2_hidden('#skF_5'('#skF_9','#skF_8'),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_8984,c_36])).

tff(c_9005,plain,(
    ! [D_29] :
      ( ~ r2_hidden(k4_tarski('#skF_5'('#skF_9','#skF_8'),D_29),'#skF_9')
      | k1_relat_1('#skF_9') = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2081,c_8993])).

tff(c_9012,plain,(
    ! [D_343] : ~ r2_hidden(k4_tarski('#skF_5'('#skF_9','#skF_8'),D_343),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_138,c_9005])).

tff(c_9016,plain,(
    ~ r2_hidden('#skF_5'('#skF_9','#skF_8'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_206,c_9012])).

tff(c_9024,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2081,c_9016])).

tff(c_9025,plain,(
    r2_hidden('#skF_11','#skF_8') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_9026,plain,(
    k1_relset_1('#skF_8','#skF_7','#skF_9') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_9074,plain,(
    ! [A_366,B_367,C_368] :
      ( k1_relset_1(A_366,B_367,C_368) = k1_relat_1(C_368)
      | ~ m1_subset_1(C_368,k1_zfmisc_1(k2_zfmisc_1(A_366,B_367))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_9081,plain,(
    k1_relset_1('#skF_8','#skF_7','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_46,c_9074])).

tff(c_9084,plain,(
    k1_relat_1('#skF_9') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9026,c_9081])).

tff(c_9107,plain,(
    ! [C_374,A_375] :
      ( r2_hidden(k4_tarski(C_374,'#skF_6'(A_375,k1_relat_1(A_375),C_374)),A_375)
      | ~ r2_hidden(C_374,k1_relat_1(A_375)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_48,plain,(
    ! [E_46] :
      ( k1_relset_1('#skF_8','#skF_7','#skF_9') != '#skF_8'
      | ~ r2_hidden(k4_tarski('#skF_11',E_46),'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_9045,plain,(
    ! [E_46] : ~ r2_hidden(k4_tarski('#skF_11',E_46),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9026,c_48])).

tff(c_9126,plain,(
    ~ r2_hidden('#skF_11',k1_relat_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_9107,c_9045])).

tff(c_9155,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9025,c_9084,c_9126])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:46:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.02/2.81  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.02/2.82  
% 8.02/2.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.02/2.82  %$ r2_hidden > r1_tarski > m1_subset_1 > k1_relset_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_11 > #skF_6 > #skF_7 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_4
% 8.02/2.82  
% 8.02/2.82  %Foreground sorts:
% 8.02/2.82  
% 8.02/2.82  
% 8.02/2.82  %Background operators:
% 8.02/2.82  
% 8.02/2.82  
% 8.02/2.82  %Foreground operators:
% 8.02/2.82  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 8.02/2.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.02/2.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.02/2.82  tff('#skF_11', type, '#skF_11': $i).
% 8.02/2.82  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 8.02/2.82  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 8.02/2.82  tff('#skF_7', type, '#skF_7': $i).
% 8.02/2.82  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.02/2.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.02/2.82  tff('#skF_10', type, '#skF_10': $i > $i).
% 8.02/2.82  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.02/2.82  tff('#skF_9', type, '#skF_9': $i).
% 8.02/2.82  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.02/2.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.02/2.82  tff('#skF_8', type, '#skF_8': $i).
% 8.02/2.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.02/2.82  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.02/2.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.02/2.82  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.02/2.82  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 8.02/2.82  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.02/2.82  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 8.02/2.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.02/2.82  
% 8.02/2.83  tff(f_73, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relset_1)).
% 8.02/2.83  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.02/2.83  tff(f_56, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 8.02/2.83  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.02/2.83  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.02/2.83  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 8.02/2.83  tff(f_44, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 8.02/2.83  tff(c_46, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.02/2.83  tff(c_128, plain, (![A_80, B_81, C_82]: (k1_relset_1(A_80, B_81, C_82)=k1_relat_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.02/2.83  tff(c_137, plain, (k1_relset_1('#skF_8', '#skF_7', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_46, c_128])).
% 8.02/2.83  tff(c_52, plain, (k1_relset_1('#skF_8', '#skF_7', '#skF_9')!='#skF_8' | r2_hidden('#skF_11', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.02/2.83  tff(c_86, plain, (k1_relset_1('#skF_8', '#skF_7', '#skF_9')!='#skF_8'), inference(splitLeft, [status(thm)], [c_52])).
% 8.02/2.83  tff(c_138, plain, (k1_relat_1('#skF_9')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_137, c_86])).
% 8.02/2.83  tff(c_1918, plain, (![A_194, B_195]: (r2_hidden(k4_tarski('#skF_3'(A_194, B_195), '#skF_4'(A_194, B_195)), A_194) | r2_hidden('#skF_5'(A_194, B_195), B_195) | k1_relat_1(A_194)=B_195)), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.02/2.83  tff(c_61, plain, (![A_51, B_52]: (r1_tarski(A_51, B_52) | ~m1_subset_1(A_51, k1_zfmisc_1(B_52)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 8.02/2.83  tff(c_69, plain, (r1_tarski('#skF_9', k2_zfmisc_1('#skF_8', '#skF_7'))), inference(resolution, [status(thm)], [c_46, c_61])).
% 8.02/2.83  tff(c_20, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.02/2.83  tff(c_73, plain, (k3_xboole_0('#skF_9', k2_zfmisc_1('#skF_8', '#skF_7'))='#skF_9'), inference(resolution, [status(thm)], [c_69, c_20])).
% 8.02/2.83  tff(c_82, plain, (![D_56, B_57, A_58]: (r2_hidden(D_56, B_57) | ~r2_hidden(D_56, k3_xboole_0(A_58, B_57)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.02/2.83  tff(c_85, plain, (![D_56]: (r2_hidden(D_56, k2_zfmisc_1('#skF_8', '#skF_7')) | ~r2_hidden(D_56, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_73, c_82])).
% 8.02/2.83  tff(c_95, plain, (![A_63, C_64, B_65, D_66]: (r2_hidden(A_63, C_64) | ~r2_hidden(k4_tarski(A_63, B_65), k2_zfmisc_1(C_64, D_66)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.02/2.83  tff(c_100, plain, (![A_63, B_65]: (r2_hidden(A_63, '#skF_8') | ~r2_hidden(k4_tarski(A_63, B_65), '#skF_9'))), inference(resolution, [status(thm)], [c_85, c_95])).
% 8.02/2.83  tff(c_2040, plain, (![B_197]: (r2_hidden('#skF_3'('#skF_9', B_197), '#skF_8') | r2_hidden('#skF_5'('#skF_9', B_197), B_197) | k1_relat_1('#skF_9')=B_197)), inference(resolution, [status(thm)], [c_1918, c_100])).
% 8.02/2.83  tff(c_40, plain, (![A_15, B_16]: (~r2_hidden('#skF_3'(A_15, B_16), B_16) | r2_hidden('#skF_5'(A_15, B_16), B_16) | k1_relat_1(A_15)=B_16)), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.02/2.83  tff(c_2051, plain, (r2_hidden('#skF_5'('#skF_9', '#skF_8'), '#skF_8') | k1_relat_1('#skF_9')='#skF_8'), inference(resolution, [status(thm)], [c_2040, c_40])).
% 8.02/2.83  tff(c_2081, plain, (r2_hidden('#skF_5'('#skF_9', '#skF_8'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_138, c_138, c_2051])).
% 8.02/2.83  tff(c_58, plain, (![D_43]: (r2_hidden(k4_tarski(D_43, '#skF_10'(D_43)), '#skF_9') | ~r2_hidden(D_43, '#skF_8') | k1_relset_1('#skF_8', '#skF_7', '#skF_9')='#skF_8')), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.02/2.83  tff(c_205, plain, (![D_43]: (r2_hidden(k4_tarski(D_43, '#skF_10'(D_43)), '#skF_9') | ~r2_hidden(D_43, '#skF_8') | k1_relat_1('#skF_9')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_137, c_58])).
% 8.02/2.83  tff(c_206, plain, (![D_43]: (r2_hidden(k4_tarski(D_43, '#skF_10'(D_43)), '#skF_9') | ~r2_hidden(D_43, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_138, c_205])).
% 8.02/2.83  tff(c_207, plain, (![D_91]: (r2_hidden(k4_tarski(D_91, '#skF_10'(D_91)), '#skF_9') | ~r2_hidden(D_91, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_138, c_205])).
% 8.02/2.83  tff(c_34, plain, (![C_30, A_15, D_33]: (r2_hidden(C_30, k1_relat_1(A_15)) | ~r2_hidden(k4_tarski(C_30, D_33), A_15))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.02/2.83  tff(c_222, plain, (![D_91]: (r2_hidden(D_91, k1_relat_1('#skF_9')) | ~r2_hidden(D_91, '#skF_8'))), inference(resolution, [status(thm)], [c_207, c_34])).
% 8.02/2.83  tff(c_32, plain, (![C_30, A_15]: (r2_hidden(k4_tarski(C_30, '#skF_6'(A_15, k1_relat_1(A_15), C_30)), A_15) | ~r2_hidden(C_30, k1_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.02/2.83  tff(c_2346, plain, (![A_209, B_210, D_211]: (r2_hidden(k4_tarski('#skF_3'(A_209, B_210), '#skF_4'(A_209, B_210)), A_209) | ~r2_hidden(k4_tarski('#skF_5'(A_209, B_210), D_211), A_209) | k1_relat_1(A_209)=B_210)), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.02/2.83  tff(c_8638, plain, (![A_335, B_336]: (r2_hidden(k4_tarski('#skF_3'(A_335, B_336), '#skF_4'(A_335, B_336)), A_335) | k1_relat_1(A_335)=B_336 | ~r2_hidden('#skF_5'(A_335, B_336), k1_relat_1(A_335)))), inference(resolution, [status(thm)], [c_32, c_2346])).
% 8.02/2.83  tff(c_8965, plain, (![B_341]: (r2_hidden('#skF_3'('#skF_9', B_341), '#skF_8') | k1_relat_1('#skF_9')=B_341 | ~r2_hidden('#skF_5'('#skF_9', B_341), k1_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_8638, c_100])).
% 8.02/2.83  tff(c_8984, plain, (![B_342]: (r2_hidden('#skF_3'('#skF_9', B_342), '#skF_8') | k1_relat_1('#skF_9')=B_342 | ~r2_hidden('#skF_5'('#skF_9', B_342), '#skF_8'))), inference(resolution, [status(thm)], [c_222, c_8965])).
% 8.02/2.83  tff(c_36, plain, (![A_15, B_16, D_29]: (~r2_hidden('#skF_3'(A_15, B_16), B_16) | ~r2_hidden(k4_tarski('#skF_5'(A_15, B_16), D_29), A_15) | k1_relat_1(A_15)=B_16)), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.02/2.83  tff(c_8993, plain, (![D_29]: (~r2_hidden(k4_tarski('#skF_5'('#skF_9', '#skF_8'), D_29), '#skF_9') | k1_relat_1('#skF_9')='#skF_8' | ~r2_hidden('#skF_5'('#skF_9', '#skF_8'), '#skF_8'))), inference(resolution, [status(thm)], [c_8984, c_36])).
% 8.02/2.83  tff(c_9005, plain, (![D_29]: (~r2_hidden(k4_tarski('#skF_5'('#skF_9', '#skF_8'), D_29), '#skF_9') | k1_relat_1('#skF_9')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2081, c_8993])).
% 8.02/2.83  tff(c_9012, plain, (![D_343]: (~r2_hidden(k4_tarski('#skF_5'('#skF_9', '#skF_8'), D_343), '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_138, c_9005])).
% 8.02/2.83  tff(c_9016, plain, (~r2_hidden('#skF_5'('#skF_9', '#skF_8'), '#skF_8')), inference(resolution, [status(thm)], [c_206, c_9012])).
% 8.02/2.83  tff(c_9024, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2081, c_9016])).
% 8.02/2.83  tff(c_9025, plain, (r2_hidden('#skF_11', '#skF_8')), inference(splitRight, [status(thm)], [c_52])).
% 8.02/2.83  tff(c_9026, plain, (k1_relset_1('#skF_8', '#skF_7', '#skF_9')='#skF_8'), inference(splitRight, [status(thm)], [c_52])).
% 8.02/2.83  tff(c_9074, plain, (![A_366, B_367, C_368]: (k1_relset_1(A_366, B_367, C_368)=k1_relat_1(C_368) | ~m1_subset_1(C_368, k1_zfmisc_1(k2_zfmisc_1(A_366, B_367))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.02/2.83  tff(c_9081, plain, (k1_relset_1('#skF_8', '#skF_7', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_46, c_9074])).
% 8.02/2.83  tff(c_9084, plain, (k1_relat_1('#skF_9')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_9026, c_9081])).
% 8.02/2.83  tff(c_9107, plain, (![C_374, A_375]: (r2_hidden(k4_tarski(C_374, '#skF_6'(A_375, k1_relat_1(A_375), C_374)), A_375) | ~r2_hidden(C_374, k1_relat_1(A_375)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.02/2.83  tff(c_48, plain, (![E_46]: (k1_relset_1('#skF_8', '#skF_7', '#skF_9')!='#skF_8' | ~r2_hidden(k4_tarski('#skF_11', E_46), '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.02/2.83  tff(c_9045, plain, (![E_46]: (~r2_hidden(k4_tarski('#skF_11', E_46), '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_9026, c_48])).
% 8.02/2.83  tff(c_9126, plain, (~r2_hidden('#skF_11', k1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_9107, c_9045])).
% 8.02/2.83  tff(c_9155, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9025, c_9084, c_9126])).
% 8.02/2.83  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.02/2.83  
% 8.02/2.83  Inference rules
% 8.02/2.83  ----------------------
% 8.02/2.83  #Ref     : 0
% 8.02/2.83  #Sup     : 2234
% 8.02/2.83  #Fact    : 0
% 8.02/2.83  #Define  : 0
% 8.02/2.83  #Split   : 12
% 8.02/2.83  #Chain   : 0
% 8.02/2.83  #Close   : 0
% 8.02/2.83  
% 8.02/2.83  Ordering : KBO
% 8.02/2.83  
% 8.02/2.83  Simplification rules
% 8.02/2.83  ----------------------
% 8.02/2.83  #Subsume      : 210
% 8.02/2.83  #Demod        : 25
% 8.02/2.83  #Tautology    : 70
% 8.02/2.83  #SimpNegUnit  : 52
% 8.02/2.83  #BackRed      : 46
% 8.02/2.83  
% 8.02/2.83  #Partial instantiations: 0
% 8.02/2.83  #Strategies tried      : 1
% 8.02/2.84  
% 8.02/2.84  Timing (in seconds)
% 8.02/2.84  ----------------------
% 8.02/2.84  Preprocessing        : 0.33
% 8.02/2.84  Parsing              : 0.16
% 8.02/2.84  CNF conversion       : 0.03
% 8.02/2.84  Main loop            : 1.74
% 8.02/2.84  Inferencing          : 0.44
% 8.02/2.84  Reduction            : 0.38
% 8.02/2.84  Demodulation         : 0.25
% 8.02/2.84  BG Simplification    : 0.08
% 8.02/2.84  Subsumption          : 0.67
% 8.02/2.84  Abstraction          : 0.09
% 8.02/2.84  MUC search           : 0.00
% 8.02/2.84  Cooper               : 0.00
% 8.02/2.84  Total                : 2.10
% 8.02/2.84  Index Insertion      : 0.00
% 8.02/2.84  Index Deletion       : 0.00
% 8.02/2.84  Index Matching       : 0.00
% 8.02/2.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
