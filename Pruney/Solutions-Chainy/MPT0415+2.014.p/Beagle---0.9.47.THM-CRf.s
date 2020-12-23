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
% DateTime   : Thu Dec  3 09:57:47 EST 2020

% Result     : Theorem 4.01s
% Output     : CNFRefutation 4.40s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 170 expanded)
%              Number of leaves         :   24 (  70 expanded)
%              Depth                    :   12
%              Number of atoms          :  101 ( 320 expanded)
%              Number of equality atoms :   22 ( 104 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k7_setfam_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ~ ( B != k1_xboole_0
            & k7_setfam_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_setfam_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => ( C = k7_setfam_1(A,B)
          <=> ! [D] :
                ( m1_subset_1(D,k1_zfmisc_1(A))
               => ( r2_hidden(D,C)
                <=> r2_hidden(k3_subset_1(A,D),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_setfam_1)).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_59,plain,(
    ! [A_31,B_32] :
      ( r1_tarski(A_31,B_32)
      | ~ m1_subset_1(A_31,k1_zfmisc_1(B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_70,plain,(
    r1_tarski('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_52,c_59])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_24,plain,(
    ! [A_9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_71,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(resolution,[status(thm)],[c_24,c_59])).

tff(c_73,plain,(
    ! [A_34,B_35] :
      ( k4_xboole_0(A_34,B_35) = k1_xboole_0
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_81,plain,(
    ! [A_9] : k4_xboole_0(k1_xboole_0,A_9) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_71,c_73])).

tff(c_486,plain,(
    ! [A_104,B_105,C_106] :
      ( r2_hidden('#skF_1'(A_104,B_105,C_106),A_104)
      | r2_hidden('#skF_2'(A_104,B_105,C_106),C_106)
      | k4_xboole_0(A_104,B_105) = C_106 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_80,plain,(
    k4_xboole_0('#skF_5',k1_zfmisc_1('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_70,c_73])).

tff(c_106,plain,(
    ! [D_44,A_45,B_46] :
      ( r2_hidden(D_44,A_45)
      | ~ r2_hidden(D_44,k4_xboole_0(A_45,B_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_112,plain,(
    ! [D_44] :
      ( r2_hidden(D_44,'#skF_5')
      | ~ r2_hidden(D_44,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_106])).

tff(c_515,plain,(
    ! [B_105,C_106] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_105,C_106),'#skF_5')
      | r2_hidden('#skF_2'(k1_xboole_0,B_105,C_106),C_106)
      | k4_xboole_0(k1_xboole_0,B_105) = C_106 ) ),
    inference(resolution,[status(thm)],[c_486,c_112])).

tff(c_1884,plain,(
    ! [B_207,C_208] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_207,C_208),'#skF_5')
      | r2_hidden('#skF_2'(k1_xboole_0,B_207,C_208),C_208)
      | k1_xboole_0 = C_208 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_515])).

tff(c_14,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1894,plain,(
    ! [B_207] :
      ( k4_xboole_0(k1_xboole_0,B_207) = '#skF_5'
      | r2_hidden('#skF_2'(k1_xboole_0,B_207,'#skF_5'),'#skF_5')
      | k1_xboole_0 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_1884,c_14])).

tff(c_1951,plain,(
    ! [B_207] :
      ( k1_xboole_0 = '#skF_5'
      | r2_hidden('#skF_2'(k1_xboole_0,B_207,'#skF_5'),'#skF_5')
      | k1_xboole_0 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_1894])).

tff(c_1952,plain,(
    ! [B_207] : r2_hidden('#skF_2'(k1_xboole_0,B_207,'#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_50,c_1951])).

tff(c_1969,plain,(
    ! [B_209] : r2_hidden('#skF_2'(k1_xboole_0,B_209,'#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_50,c_1951])).

tff(c_44,plain,(
    ! [A_23,B_24] :
      ( m1_subset_1(A_23,k1_zfmisc_1(B_24))
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_114,plain,(
    ! [A_48,C_49,B_50] :
      ( m1_subset_1(A_48,C_49)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(C_49))
      | ~ r2_hidden(A_48,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_121,plain,(
    ! [A_48,B_24,A_23] :
      ( m1_subset_1(A_48,B_24)
      | ~ r2_hidden(A_48,A_23)
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(resolution,[status(thm)],[c_44,c_114])).

tff(c_1983,plain,(
    ! [B_209,B_24] :
      ( m1_subset_1('#skF_2'(k1_xboole_0,B_209,'#skF_5'),B_24)
      | ~ r1_tarski('#skF_5',B_24) ) ),
    inference(resolution,[status(thm)],[c_1969,c_121])).

tff(c_48,plain,(
    k7_setfam_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_136,plain,(
    ! [A_60,B_61] :
      ( k7_setfam_1(A_60,k7_setfam_1(A_60,B_61)) = B_61
      | ~ m1_subset_1(B_61,k1_zfmisc_1(k1_zfmisc_1(A_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_141,plain,(
    k7_setfam_1('#skF_4',k7_setfam_1('#skF_4','#skF_5')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_52,c_136])).

tff(c_147,plain,(
    k7_setfam_1('#skF_4',k1_xboole_0) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_141])).

tff(c_2190,plain,(
    ! [A_223,D_224,B_225] :
      ( r2_hidden(k3_subset_1(A_223,D_224),B_225)
      | ~ r2_hidden(D_224,k7_setfam_1(A_223,B_225))
      | ~ m1_subset_1(D_224,k1_zfmisc_1(A_223))
      | ~ m1_subset_1(k7_setfam_1(A_223,B_225),k1_zfmisc_1(k1_zfmisc_1(A_223)))
      | ~ m1_subset_1(B_225,k1_zfmisc_1(k1_zfmisc_1(A_223))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2203,plain,(
    ! [D_224] :
      ( r2_hidden(k3_subset_1('#skF_4',D_224),k1_xboole_0)
      | ~ r2_hidden(D_224,k7_setfam_1('#skF_4',k1_xboole_0))
      | ~ m1_subset_1(D_224,k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_4')))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_2190])).

tff(c_2213,plain,(
    ! [D_224] :
      ( r2_hidden(k3_subset_1('#skF_4',D_224),k1_xboole_0)
      | ~ r2_hidden(D_224,'#skF_5')
      | ~ m1_subset_1(D_224,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_52,c_147,c_2203])).

tff(c_2266,plain,(
    ! [D_231] :
      ( r2_hidden(k3_subset_1('#skF_4',D_231),k1_xboole_0)
      | ~ r2_hidden(D_231,'#skF_5')
      | ~ m1_subset_1(D_231,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_52,c_147,c_2203])).

tff(c_98,plain,(
    ! [D_39,B_40,A_41] :
      ( ~ r2_hidden(D_39,B_40)
      | ~ r2_hidden(D_39,k4_xboole_0(A_41,B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_101,plain,(
    ! [D_39,A_9] :
      ( ~ r2_hidden(D_39,A_9)
      | ~ r2_hidden(D_39,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_98])).

tff(c_2486,plain,(
    ! [D_243] :
      ( ~ r2_hidden(k3_subset_1('#skF_4',D_243),k1_xboole_0)
      | ~ r2_hidden(D_243,'#skF_5')
      | ~ m1_subset_1(D_243,k1_zfmisc_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_2266,c_101])).

tff(c_2491,plain,(
    ! [D_244] :
      ( ~ r2_hidden(D_244,'#skF_5')
      | ~ m1_subset_1(D_244,k1_zfmisc_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_2213,c_2486])).

tff(c_2499,plain,(
    ! [B_209] :
      ( ~ r2_hidden('#skF_2'(k1_xboole_0,B_209,'#skF_5'),'#skF_5')
      | ~ r1_tarski('#skF_5',k1_zfmisc_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1983,c_2491])).

tff(c_2533,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1952,c_2499])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:48:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.01/1.78  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.01/1.79  
% 4.01/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.37/1.79  %$ r2_hidden > r1_tarski > m1_subset_1 > k7_setfam_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 4.37/1.79  
% 4.37/1.79  %Foreground sorts:
% 4.37/1.79  
% 4.37/1.79  
% 4.37/1.79  %Background operators:
% 4.37/1.79  
% 4.37/1.79  
% 4.37/1.79  %Foreground operators:
% 4.37/1.79  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.37/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.37/1.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.37/1.79  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.37/1.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.37/1.79  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 4.37/1.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.37/1.79  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.37/1.79  tff('#skF_5', type, '#skF_5': $i).
% 4.37/1.79  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.37/1.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.37/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.37/1.79  tff('#skF_4', type, '#skF_4': $i).
% 4.37/1.79  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.37/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.37/1.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.37/1.79  
% 4.40/1.80  tff(f_78, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_setfam_1)).
% 4.40/1.80  tff(f_63, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.40/1.80  tff(f_41, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 4.40/1.80  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.40/1.80  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 4.40/1.80  tff(f_69, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 4.40/1.80  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 4.40/1.80  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((C = k7_setfam_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, C) <=> r2_hidden(k3_subset_1(A, D), B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_setfam_1)).
% 4.40/1.80  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.40/1.80  tff(c_59, plain, (![A_31, B_32]: (r1_tarski(A_31, B_32) | ~m1_subset_1(A_31, k1_zfmisc_1(B_32)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.40/1.80  tff(c_70, plain, (r1_tarski('#skF_5', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_52, c_59])).
% 4.40/1.80  tff(c_50, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.40/1.80  tff(c_24, plain, (![A_9]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.40/1.80  tff(c_71, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(resolution, [status(thm)], [c_24, c_59])).
% 4.40/1.80  tff(c_73, plain, (![A_34, B_35]: (k4_xboole_0(A_34, B_35)=k1_xboole_0 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.40/1.80  tff(c_81, plain, (![A_9]: (k4_xboole_0(k1_xboole_0, A_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_71, c_73])).
% 4.40/1.80  tff(c_486, plain, (![A_104, B_105, C_106]: (r2_hidden('#skF_1'(A_104, B_105, C_106), A_104) | r2_hidden('#skF_2'(A_104, B_105, C_106), C_106) | k4_xboole_0(A_104, B_105)=C_106)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.40/1.80  tff(c_80, plain, (k4_xboole_0('#skF_5', k1_zfmisc_1('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_70, c_73])).
% 4.40/1.80  tff(c_106, plain, (![D_44, A_45, B_46]: (r2_hidden(D_44, A_45) | ~r2_hidden(D_44, k4_xboole_0(A_45, B_46)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.40/1.80  tff(c_112, plain, (![D_44]: (r2_hidden(D_44, '#skF_5') | ~r2_hidden(D_44, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_80, c_106])).
% 4.40/1.80  tff(c_515, plain, (![B_105, C_106]: (r2_hidden('#skF_1'(k1_xboole_0, B_105, C_106), '#skF_5') | r2_hidden('#skF_2'(k1_xboole_0, B_105, C_106), C_106) | k4_xboole_0(k1_xboole_0, B_105)=C_106)), inference(resolution, [status(thm)], [c_486, c_112])).
% 4.40/1.80  tff(c_1884, plain, (![B_207, C_208]: (r2_hidden('#skF_1'(k1_xboole_0, B_207, C_208), '#skF_5') | r2_hidden('#skF_2'(k1_xboole_0, B_207, C_208), C_208) | k1_xboole_0=C_208)), inference(demodulation, [status(thm), theory('equality')], [c_81, c_515])).
% 4.40/1.80  tff(c_14, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.40/1.80  tff(c_1894, plain, (![B_207]: (k4_xboole_0(k1_xboole_0, B_207)='#skF_5' | r2_hidden('#skF_2'(k1_xboole_0, B_207, '#skF_5'), '#skF_5') | k1_xboole_0='#skF_5')), inference(resolution, [status(thm)], [c_1884, c_14])).
% 4.40/1.80  tff(c_1951, plain, (![B_207]: (k1_xboole_0='#skF_5' | r2_hidden('#skF_2'(k1_xboole_0, B_207, '#skF_5'), '#skF_5') | k1_xboole_0='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_1894])).
% 4.40/1.80  tff(c_1952, plain, (![B_207]: (r2_hidden('#skF_2'(k1_xboole_0, B_207, '#skF_5'), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_50, c_50, c_1951])).
% 4.40/1.80  tff(c_1969, plain, (![B_209]: (r2_hidden('#skF_2'(k1_xboole_0, B_209, '#skF_5'), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_50, c_50, c_1951])).
% 4.40/1.80  tff(c_44, plain, (![A_23, B_24]: (m1_subset_1(A_23, k1_zfmisc_1(B_24)) | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.40/1.80  tff(c_114, plain, (![A_48, C_49, B_50]: (m1_subset_1(A_48, C_49) | ~m1_subset_1(B_50, k1_zfmisc_1(C_49)) | ~r2_hidden(A_48, B_50))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.40/1.80  tff(c_121, plain, (![A_48, B_24, A_23]: (m1_subset_1(A_48, B_24) | ~r2_hidden(A_48, A_23) | ~r1_tarski(A_23, B_24))), inference(resolution, [status(thm)], [c_44, c_114])).
% 4.40/1.80  tff(c_1983, plain, (![B_209, B_24]: (m1_subset_1('#skF_2'(k1_xboole_0, B_209, '#skF_5'), B_24) | ~r1_tarski('#skF_5', B_24))), inference(resolution, [status(thm)], [c_1969, c_121])).
% 4.40/1.80  tff(c_48, plain, (k7_setfam_1('#skF_4', '#skF_5')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.40/1.80  tff(c_136, plain, (![A_60, B_61]: (k7_setfam_1(A_60, k7_setfam_1(A_60, B_61))=B_61 | ~m1_subset_1(B_61, k1_zfmisc_1(k1_zfmisc_1(A_60))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.40/1.80  tff(c_141, plain, (k7_setfam_1('#skF_4', k7_setfam_1('#skF_4', '#skF_5'))='#skF_5'), inference(resolution, [status(thm)], [c_52, c_136])).
% 4.40/1.80  tff(c_147, plain, (k7_setfam_1('#skF_4', k1_xboole_0)='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_141])).
% 4.40/1.80  tff(c_2190, plain, (![A_223, D_224, B_225]: (r2_hidden(k3_subset_1(A_223, D_224), B_225) | ~r2_hidden(D_224, k7_setfam_1(A_223, B_225)) | ~m1_subset_1(D_224, k1_zfmisc_1(A_223)) | ~m1_subset_1(k7_setfam_1(A_223, B_225), k1_zfmisc_1(k1_zfmisc_1(A_223))) | ~m1_subset_1(B_225, k1_zfmisc_1(k1_zfmisc_1(A_223))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.40/1.80  tff(c_2203, plain, (![D_224]: (r2_hidden(k3_subset_1('#skF_4', D_224), k1_xboole_0) | ~r2_hidden(D_224, k7_setfam_1('#skF_4', k1_xboole_0)) | ~m1_subset_1(D_224, k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_147, c_2190])).
% 4.40/1.80  tff(c_2213, plain, (![D_224]: (r2_hidden(k3_subset_1('#skF_4', D_224), k1_xboole_0) | ~r2_hidden(D_224, '#skF_5') | ~m1_subset_1(D_224, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_52, c_147, c_2203])).
% 4.40/1.80  tff(c_2266, plain, (![D_231]: (r2_hidden(k3_subset_1('#skF_4', D_231), k1_xboole_0) | ~r2_hidden(D_231, '#skF_5') | ~m1_subset_1(D_231, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_52, c_147, c_2203])).
% 4.40/1.80  tff(c_98, plain, (![D_39, B_40, A_41]: (~r2_hidden(D_39, B_40) | ~r2_hidden(D_39, k4_xboole_0(A_41, B_40)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.40/1.80  tff(c_101, plain, (![D_39, A_9]: (~r2_hidden(D_39, A_9) | ~r2_hidden(D_39, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_81, c_98])).
% 4.40/1.80  tff(c_2486, plain, (![D_243]: (~r2_hidden(k3_subset_1('#skF_4', D_243), k1_xboole_0) | ~r2_hidden(D_243, '#skF_5') | ~m1_subset_1(D_243, k1_zfmisc_1('#skF_4')))), inference(resolution, [status(thm)], [c_2266, c_101])).
% 4.40/1.80  tff(c_2491, plain, (![D_244]: (~r2_hidden(D_244, '#skF_5') | ~m1_subset_1(D_244, k1_zfmisc_1('#skF_4')))), inference(resolution, [status(thm)], [c_2213, c_2486])).
% 4.40/1.80  tff(c_2499, plain, (![B_209]: (~r2_hidden('#skF_2'(k1_xboole_0, B_209, '#skF_5'), '#skF_5') | ~r1_tarski('#skF_5', k1_zfmisc_1('#skF_4')))), inference(resolution, [status(thm)], [c_1983, c_2491])).
% 4.40/1.80  tff(c_2533, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_1952, c_2499])).
% 4.40/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.40/1.80  
% 4.40/1.80  Inference rules
% 4.40/1.80  ----------------------
% 4.40/1.80  #Ref     : 0
% 4.40/1.80  #Sup     : 562
% 4.40/1.80  #Fact    : 0
% 4.40/1.80  #Define  : 0
% 4.40/1.80  #Split   : 2
% 4.40/1.80  #Chain   : 0
% 4.40/1.80  #Close   : 0
% 4.40/1.80  
% 4.40/1.80  Ordering : KBO
% 4.40/1.80  
% 4.40/1.80  Simplification rules
% 4.40/1.80  ----------------------
% 4.40/1.80  #Subsume      : 99
% 4.40/1.80  #Demod        : 139
% 4.40/1.80  #Tautology    : 166
% 4.40/1.80  #SimpNegUnit  : 11
% 4.40/1.80  #BackRed      : 4
% 4.40/1.80  
% 4.40/1.80  #Partial instantiations: 0
% 4.40/1.80  #Strategies tried      : 1
% 4.40/1.80  
% 4.40/1.80  Timing (in seconds)
% 4.40/1.80  ----------------------
% 4.45/1.80  Preprocessing        : 0.31
% 4.45/1.81  Parsing              : 0.16
% 4.45/1.81  CNF conversion       : 0.02
% 4.45/1.81  Main loop            : 0.69
% 4.45/1.81  Inferencing          : 0.24
% 4.45/1.81  Reduction            : 0.19
% 4.45/1.81  Demodulation         : 0.12
% 4.45/1.81  BG Simplification    : 0.03
% 4.45/1.81  Subsumption          : 0.18
% 4.45/1.81  Abstraction          : 0.04
% 4.45/1.81  MUC search           : 0.00
% 4.45/1.81  Cooper               : 0.00
% 4.45/1.81  Total                : 1.03
% 4.46/1.81  Index Insertion      : 0.00
% 4.46/1.81  Index Deletion       : 0.00
% 4.46/1.81  Index Matching       : 0.00
% 4.46/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
