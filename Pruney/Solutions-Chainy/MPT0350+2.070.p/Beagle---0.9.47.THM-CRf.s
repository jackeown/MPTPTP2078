%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:34 EST 2020

% Result     : Theorem 19.12s
% Output     : CNFRefutation 19.12s
% Verified   : 
% Statistics : Number of formulae       :   73 (  88 expanded)
%              Number of leaves         :   38 (  47 expanded)
%              Depth                    :    8
%              Number of atoms          :   88 ( 118 expanded)
%              Number of equality atoms :   26 (  34 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_8 > #skF_3 > #skF_2 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_84,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_102,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_91,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_62,plain,(
    ! [A_35] : k2_subset_1(A_35) = A_35 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_70,plain,(
    k4_subset_1('#skF_7','#skF_8',k3_subset_1('#skF_7','#skF_8')) != k2_subset_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_73,plain,(
    k4_subset_1('#skF_7','#skF_8',k3_subset_1('#skF_7','#skF_8')) != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_70])).

tff(c_72,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_66,plain,(
    ! [A_38] : ~ v1_xboole_0(k1_zfmisc_1(A_38)) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_316,plain,(
    ! [B_91,A_92] :
      ( r2_hidden(B_91,A_92)
      | ~ m1_subset_1(B_91,A_92)
      | v1_xboole_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_40,plain,(
    ! [C_30,A_26] :
      ( r1_tarski(C_30,A_26)
      | ~ r2_hidden(C_30,k1_zfmisc_1(A_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_335,plain,(
    ! [B_91,A_26] :
      ( r1_tarski(B_91,A_26)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(A_26))
      | v1_xboole_0(k1_zfmisc_1(A_26)) ) ),
    inference(resolution,[status(thm)],[c_316,c_40])).

tff(c_347,plain,(
    ! [B_93,A_94] :
      ( r1_tarski(B_93,A_94)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(A_94)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_335])).

tff(c_367,plain,(
    r1_tarski('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_72,c_347])).

tff(c_34,plain,(
    ! [A_20,B_21] :
      ( k3_xboole_0(A_20,B_21) = A_20
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_371,plain,(
    k3_xboole_0('#skF_8','#skF_7') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_367,c_34])).

tff(c_549,plain,(
    ! [A_104,B_105] :
      ( k4_xboole_0(A_104,B_105) = k3_subset_1(A_104,B_105)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(A_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_569,plain,(
    k4_xboole_0('#skF_7','#skF_8') = k3_subset_1('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_72,c_549])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_278,plain,(
    ! [A_85,B_86] : k2_xboole_0(k3_xboole_0(A_85,B_86),k4_xboole_0(A_85,B_86)) = A_85 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_293,plain,(
    ! [A_1,B_2] : k2_xboole_0(k3_xboole_0(A_1,B_2),k4_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_278])).

tff(c_575,plain,(
    k2_xboole_0(k3_xboole_0('#skF_8','#skF_7'),k3_subset_1('#skF_7','#skF_8')) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_569,c_293])).

tff(c_587,plain,(
    k2_xboole_0('#skF_8',k3_subset_1('#skF_7','#skF_8')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_575])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_2'(A_7,B_8),A_7)
      | r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_18,plain,(
    ! [D_17,A_12,B_13] :
      ( r2_hidden(D_17,A_12)
      | ~ r2_hidden(D_17,k4_xboole_0(A_12,B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_595,plain,(
    ! [D_106] :
      ( r2_hidden(D_106,'#skF_7')
      | ~ r2_hidden(D_106,k3_subset_1('#skF_7','#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_569,c_18])).

tff(c_4469,plain,(
    ! [B_315] :
      ( r2_hidden('#skF_2'(k3_subset_1('#skF_7','#skF_8'),B_315),'#skF_7')
      | r1_tarski(k3_subset_1('#skF_7','#skF_8'),B_315) ) ),
    inference(resolution,[status(thm)],[c_12,c_595])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( ~ r2_hidden('#skF_2'(A_7,B_8),B_8)
      | r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4486,plain,(
    r1_tarski(k3_subset_1('#skF_7','#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_4469,c_10])).

tff(c_42,plain,(
    ! [C_30,A_26] :
      ( r2_hidden(C_30,k1_zfmisc_1(A_26))
      | ~ r1_tarski(C_30,A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_189,plain,(
    ! [B_66,A_67] :
      ( m1_subset_1(B_66,A_67)
      | ~ r2_hidden(B_66,A_67)
      | v1_xboole_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_192,plain,(
    ! [C_30,A_26] :
      ( m1_subset_1(C_30,k1_zfmisc_1(A_26))
      | v1_xboole_0(k1_zfmisc_1(A_26))
      | ~ r1_tarski(C_30,A_26) ) ),
    inference(resolution,[status(thm)],[c_42,c_189])).

tff(c_198,plain,(
    ! [C_30,A_26] :
      ( m1_subset_1(C_30,k1_zfmisc_1(A_26))
      | ~ r1_tarski(C_30,A_26) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_192])).

tff(c_1361,plain,(
    ! [A_154,B_155,C_156] :
      ( k4_subset_1(A_154,B_155,C_156) = k2_xboole_0(B_155,C_156)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(A_154))
      | ~ m1_subset_1(B_155,k1_zfmisc_1(A_154)) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_54787,plain,(
    ! [A_1306,B_1307,C_1308] :
      ( k4_subset_1(A_1306,B_1307,C_1308) = k2_xboole_0(B_1307,C_1308)
      | ~ m1_subset_1(B_1307,k1_zfmisc_1(A_1306))
      | ~ r1_tarski(C_1308,A_1306) ) ),
    inference(resolution,[status(thm)],[c_198,c_1361])).

tff(c_54925,plain,(
    ! [C_1310] :
      ( k4_subset_1('#skF_7','#skF_8',C_1310) = k2_xboole_0('#skF_8',C_1310)
      | ~ r1_tarski(C_1310,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_72,c_54787])).

tff(c_55149,plain,(
    k4_subset_1('#skF_7','#skF_8',k3_subset_1('#skF_7','#skF_8')) = k2_xboole_0('#skF_8',k3_subset_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_4486,c_54925])).

tff(c_55254,plain,(
    k4_subset_1('#skF_7','#skF_8',k3_subset_1('#skF_7','#skF_8')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_587,c_55149])).

tff(c_55256,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_55254])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:32:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 19.12/10.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.12/10.27  
% 19.12/10.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.12/10.28  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_8 > #skF_3 > #skF_2 > #skF_5
% 19.12/10.28  
% 19.12/10.28  %Foreground sorts:
% 19.12/10.28  
% 19.12/10.28  
% 19.12/10.28  %Background operators:
% 19.12/10.28  
% 19.12/10.28  
% 19.12/10.28  %Foreground operators:
% 19.12/10.28  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 19.12/10.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 19.12/10.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 19.12/10.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 19.12/10.28  tff('#skF_1', type, '#skF_1': $i > $i).
% 19.12/10.28  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 19.12/10.28  tff('#skF_7', type, '#skF_7': $i).
% 19.12/10.28  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 19.12/10.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 19.12/10.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 19.12/10.28  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 19.12/10.28  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 19.12/10.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 19.12/10.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 19.12/10.28  tff('#skF_8', type, '#skF_8': $i).
% 19.12/10.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 19.12/10.28  tff(k3_tarski, type, k3_tarski: $i > $i).
% 19.12/10.28  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 19.12/10.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 19.12/10.28  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 19.12/10.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 19.12/10.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 19.12/10.28  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 19.12/10.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 19.12/10.28  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 19.12/10.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 19.12/10.28  
% 19.12/10.29  tff(f_84, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 19.12/10.29  tff(f_102, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 19.12/10.29  tff(f_91, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 19.12/10.29  tff(f_82, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 19.12/10.29  tff(f_67, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 19.12/10.29  tff(f_56, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 19.12/10.29  tff(f_88, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 19.12/10.29  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 19.12/10.29  tff(f_58, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 19.12/10.29  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 19.12/10.29  tff(f_50, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 19.12/10.29  tff(f_97, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 19.12/10.29  tff(c_62, plain, (![A_35]: (k2_subset_1(A_35)=A_35)), inference(cnfTransformation, [status(thm)], [f_84])).
% 19.12/10.29  tff(c_70, plain, (k4_subset_1('#skF_7', '#skF_8', k3_subset_1('#skF_7', '#skF_8'))!=k2_subset_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_102])).
% 19.12/10.29  tff(c_73, plain, (k4_subset_1('#skF_7', '#skF_8', k3_subset_1('#skF_7', '#skF_8'))!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_70])).
% 19.12/10.29  tff(c_72, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 19.12/10.29  tff(c_66, plain, (![A_38]: (~v1_xboole_0(k1_zfmisc_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 19.12/10.29  tff(c_316, plain, (![B_91, A_92]: (r2_hidden(B_91, A_92) | ~m1_subset_1(B_91, A_92) | v1_xboole_0(A_92))), inference(cnfTransformation, [status(thm)], [f_82])).
% 19.12/10.29  tff(c_40, plain, (![C_30, A_26]: (r1_tarski(C_30, A_26) | ~r2_hidden(C_30, k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 19.12/10.29  tff(c_335, plain, (![B_91, A_26]: (r1_tarski(B_91, A_26) | ~m1_subset_1(B_91, k1_zfmisc_1(A_26)) | v1_xboole_0(k1_zfmisc_1(A_26)))), inference(resolution, [status(thm)], [c_316, c_40])).
% 19.12/10.29  tff(c_347, plain, (![B_93, A_94]: (r1_tarski(B_93, A_94) | ~m1_subset_1(B_93, k1_zfmisc_1(A_94)))), inference(negUnitSimplification, [status(thm)], [c_66, c_335])).
% 19.12/10.29  tff(c_367, plain, (r1_tarski('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_72, c_347])).
% 19.12/10.29  tff(c_34, plain, (![A_20, B_21]: (k3_xboole_0(A_20, B_21)=A_20 | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_56])).
% 19.12/10.29  tff(c_371, plain, (k3_xboole_0('#skF_8', '#skF_7')='#skF_8'), inference(resolution, [status(thm)], [c_367, c_34])).
% 19.12/10.29  tff(c_549, plain, (![A_104, B_105]: (k4_xboole_0(A_104, B_105)=k3_subset_1(A_104, B_105) | ~m1_subset_1(B_105, k1_zfmisc_1(A_104)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 19.12/10.29  tff(c_569, plain, (k4_xboole_0('#skF_7', '#skF_8')=k3_subset_1('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_72, c_549])).
% 19.12/10.29  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 19.12/10.29  tff(c_278, plain, (![A_85, B_86]: (k2_xboole_0(k3_xboole_0(A_85, B_86), k4_xboole_0(A_85, B_86))=A_85)), inference(cnfTransformation, [status(thm)], [f_58])).
% 19.12/10.29  tff(c_293, plain, (![A_1, B_2]: (k2_xboole_0(k3_xboole_0(A_1, B_2), k4_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_278])).
% 19.12/10.29  tff(c_575, plain, (k2_xboole_0(k3_xboole_0('#skF_8', '#skF_7'), k3_subset_1('#skF_7', '#skF_8'))='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_569, c_293])).
% 19.12/10.29  tff(c_587, plain, (k2_xboole_0('#skF_8', k3_subset_1('#skF_7', '#skF_8'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_371, c_575])).
% 19.12/10.29  tff(c_12, plain, (![A_7, B_8]: (r2_hidden('#skF_2'(A_7, B_8), A_7) | r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 19.12/10.29  tff(c_18, plain, (![D_17, A_12, B_13]: (r2_hidden(D_17, A_12) | ~r2_hidden(D_17, k4_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 19.12/10.29  tff(c_595, plain, (![D_106]: (r2_hidden(D_106, '#skF_7') | ~r2_hidden(D_106, k3_subset_1('#skF_7', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_569, c_18])).
% 19.12/10.29  tff(c_4469, plain, (![B_315]: (r2_hidden('#skF_2'(k3_subset_1('#skF_7', '#skF_8'), B_315), '#skF_7') | r1_tarski(k3_subset_1('#skF_7', '#skF_8'), B_315))), inference(resolution, [status(thm)], [c_12, c_595])).
% 19.12/10.29  tff(c_10, plain, (![A_7, B_8]: (~r2_hidden('#skF_2'(A_7, B_8), B_8) | r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 19.12/10.29  tff(c_4486, plain, (r1_tarski(k3_subset_1('#skF_7', '#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_4469, c_10])).
% 19.12/10.29  tff(c_42, plain, (![C_30, A_26]: (r2_hidden(C_30, k1_zfmisc_1(A_26)) | ~r1_tarski(C_30, A_26))), inference(cnfTransformation, [status(thm)], [f_67])).
% 19.12/10.29  tff(c_189, plain, (![B_66, A_67]: (m1_subset_1(B_66, A_67) | ~r2_hidden(B_66, A_67) | v1_xboole_0(A_67))), inference(cnfTransformation, [status(thm)], [f_82])).
% 19.12/10.29  tff(c_192, plain, (![C_30, A_26]: (m1_subset_1(C_30, k1_zfmisc_1(A_26)) | v1_xboole_0(k1_zfmisc_1(A_26)) | ~r1_tarski(C_30, A_26))), inference(resolution, [status(thm)], [c_42, c_189])).
% 19.12/10.29  tff(c_198, plain, (![C_30, A_26]: (m1_subset_1(C_30, k1_zfmisc_1(A_26)) | ~r1_tarski(C_30, A_26))), inference(negUnitSimplification, [status(thm)], [c_66, c_192])).
% 19.12/10.29  tff(c_1361, plain, (![A_154, B_155, C_156]: (k4_subset_1(A_154, B_155, C_156)=k2_xboole_0(B_155, C_156) | ~m1_subset_1(C_156, k1_zfmisc_1(A_154)) | ~m1_subset_1(B_155, k1_zfmisc_1(A_154)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 19.12/10.29  tff(c_54787, plain, (![A_1306, B_1307, C_1308]: (k4_subset_1(A_1306, B_1307, C_1308)=k2_xboole_0(B_1307, C_1308) | ~m1_subset_1(B_1307, k1_zfmisc_1(A_1306)) | ~r1_tarski(C_1308, A_1306))), inference(resolution, [status(thm)], [c_198, c_1361])).
% 19.12/10.29  tff(c_54925, plain, (![C_1310]: (k4_subset_1('#skF_7', '#skF_8', C_1310)=k2_xboole_0('#skF_8', C_1310) | ~r1_tarski(C_1310, '#skF_7'))), inference(resolution, [status(thm)], [c_72, c_54787])).
% 19.12/10.29  tff(c_55149, plain, (k4_subset_1('#skF_7', '#skF_8', k3_subset_1('#skF_7', '#skF_8'))=k2_xboole_0('#skF_8', k3_subset_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_4486, c_54925])).
% 19.12/10.29  tff(c_55254, plain, (k4_subset_1('#skF_7', '#skF_8', k3_subset_1('#skF_7', '#skF_8'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_587, c_55149])).
% 19.12/10.29  tff(c_55256, plain, $false, inference(negUnitSimplification, [status(thm)], [c_73, c_55254])).
% 19.12/10.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.12/10.29  
% 19.12/10.29  Inference rules
% 19.12/10.29  ----------------------
% 19.12/10.29  #Ref     : 0
% 19.12/10.29  #Sup     : 14145
% 19.12/10.29  #Fact    : 2
% 19.12/10.29  #Define  : 0
% 19.12/10.29  #Split   : 16
% 19.12/10.29  #Chain   : 0
% 19.12/10.29  #Close   : 0
% 19.12/10.29  
% 19.12/10.29  Ordering : KBO
% 19.12/10.29  
% 19.12/10.29  Simplification rules
% 19.12/10.29  ----------------------
% 19.12/10.29  #Subsume      : 4633
% 19.12/10.29  #Demod        : 5061
% 19.12/10.29  #Tautology    : 2962
% 19.12/10.29  #SimpNegUnit  : 389
% 19.12/10.29  #BackRed      : 16
% 19.12/10.29  
% 19.12/10.29  #Partial instantiations: 0
% 19.12/10.29  #Strategies tried      : 1
% 19.12/10.29  
% 19.12/10.29  Timing (in seconds)
% 19.12/10.29  ----------------------
% 19.12/10.29  Preprocessing        : 0.34
% 19.12/10.29  Parsing              : 0.17
% 19.12/10.29  CNF conversion       : 0.03
% 19.12/10.29  Main loop            : 9.19
% 19.12/10.29  Inferencing          : 1.49
% 19.12/10.29  Reduction            : 4.15
% 19.12/10.29  Demodulation         : 3.19
% 19.12/10.29  BG Simplification    : 0.16
% 19.12/10.29  Subsumption          : 2.75
% 19.12/10.29  Abstraction          : 0.26
% 19.12/10.29  MUC search           : 0.00
% 19.12/10.29  Cooper               : 0.00
% 19.12/10.29  Total                : 9.56
% 19.12/10.29  Index Insertion      : 0.00
% 19.12/10.29  Index Deletion       : 0.00
% 19.12/10.29  Index Matching       : 0.00
% 19.12/10.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
