%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:14 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :   68 (  83 expanded)
%              Number of leaves         :   33 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :   85 ( 118 expanded)
%              Number of equality atoms :   36 (  48 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_tarski > k3_xboole_0 > k2_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_81,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_37,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_48,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_41,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(c_38,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_40,plain,
    ( k11_relat_1('#skF_7','#skF_6') = k1_xboole_0
    | ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_157,plain,(
    ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_46,plain,
    ( r2_hidden('#skF_6',k1_relat_1('#skF_7'))
    | k11_relat_1('#skF_7','#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_207,plain,(
    k11_relat_1('#skF_7','#skF_6') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_157,c_46])).

tff(c_6,plain,(
    ! [A_3] :
      ( r2_hidden('#skF_1'(A_3),A_3)
      | k1_xboole_0 = A_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_369,plain,(
    ! [A_89,B_90,C_91] :
      ( r2_hidden(k4_tarski(A_89,B_90),C_91)
      | ~ r2_hidden(B_90,k11_relat_1(C_91,A_89))
      | ~ v1_relat_1(C_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_20,plain,(
    ! [C_31,A_16,D_34] :
      ( r2_hidden(C_31,k1_relat_1(A_16))
      | ~ r2_hidden(k4_tarski(C_31,D_34),A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_383,plain,(
    ! [A_95,C_96,B_97] :
      ( r2_hidden(A_95,k1_relat_1(C_96))
      | ~ r2_hidden(B_97,k11_relat_1(C_96,A_95))
      | ~ v1_relat_1(C_96) ) ),
    inference(resolution,[status(thm)],[c_369,c_20])).

tff(c_392,plain,(
    ! [A_98,C_99] :
      ( r2_hidden(A_98,k1_relat_1(C_99))
      | ~ v1_relat_1(C_99)
      | k11_relat_1(C_99,A_98) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_383])).

tff(c_403,plain,
    ( ~ v1_relat_1('#skF_7')
    | k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_392,c_157])).

tff(c_408,plain,(
    k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_403])).

tff(c_410,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_207,c_408])).

tff(c_411,plain,(
    k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_16,plain,(
    ! [A_13,B_15] :
      ( k9_relat_1(A_13,k1_tarski(B_15)) = k11_relat_1(A_13,B_15)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_412,plain,(
    r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_619,plain,(
    ! [B_133,A_134] :
      ( r1_xboole_0(k1_relat_1(B_133),A_134)
      | k9_relat_1(B_133,A_134) != k1_xboole_0
      | ~ v1_relat_1(B_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_630,plain,(
    ! [B_139,A_140] :
      ( k3_xboole_0(k1_relat_1(B_139),A_140) = k1_xboole_0
      | k9_relat_1(B_139,A_140) != k1_xboole_0
      | ~ v1_relat_1(B_139) ) ),
    inference(resolution,[status(thm)],[c_619,c_2])).

tff(c_8,plain,(
    ! [B_6,A_5] : k2_tarski(B_6,A_5) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_96,plain,(
    ! [A_48,B_49] : k1_setfam_1(k2_tarski(A_48,B_49)) = k3_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_131,plain,(
    ! [B_51,A_52] : k1_setfam_1(k2_tarski(B_51,A_52)) = k3_xboole_0(A_52,B_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_96])).

tff(c_14,plain,(
    ! [A_11,B_12] : k1_setfam_1(k2_tarski(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_137,plain,(
    ! [B_51,A_52] : k3_xboole_0(B_51,A_52) = k3_xboole_0(A_52,B_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_14])).

tff(c_785,plain,(
    ! [A_159,B_160] :
      ( k3_xboole_0(A_159,k1_relat_1(B_160)) = k1_xboole_0
      | k9_relat_1(B_160,A_159) != k1_xboole_0
      | ~ v1_relat_1(B_160) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_630,c_137])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_450,plain,(
    ! [A_102,C_103,B_104] :
      ( ~ r2_hidden(A_102,C_103)
      | ~ r1_xboole_0(k2_tarski(A_102,B_104),C_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_465,plain,(
    ! [A_105,C_106] :
      ( ~ r2_hidden(A_105,C_106)
      | ~ r1_xboole_0(k1_tarski(A_105),C_106) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_450])).

tff(c_470,plain,(
    ! [A_105,B_2] :
      ( ~ r2_hidden(A_105,B_2)
      | k3_xboole_0(k1_tarski(A_105),B_2) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_465])).

tff(c_885,plain,(
    ! [A_170,B_171] :
      ( ~ r2_hidden(A_170,k1_relat_1(B_171))
      | k9_relat_1(B_171,k1_tarski(A_170)) != k1_xboole_0
      | ~ v1_relat_1(B_171) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_785,c_470])).

tff(c_899,plain,
    ( k9_relat_1('#skF_7',k1_tarski('#skF_6')) != k1_xboole_0
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_412,c_885])).

tff(c_909,plain,(
    k9_relat_1('#skF_7',k1_tarski('#skF_6')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_899])).

tff(c_913,plain,
    ( k11_relat_1('#skF_7','#skF_6') != k1_xboole_0
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_909])).

tff(c_916,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_411,c_913])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:18:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.59/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.44  
% 2.59/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.44  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_tarski > k3_xboole_0 > k2_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_4
% 2.59/1.44  
% 2.59/1.44  %Foreground sorts:
% 2.59/1.44  
% 2.59/1.44  
% 2.59/1.44  %Background operators:
% 2.59/1.44  
% 2.59/1.44  
% 2.59/1.44  %Foreground operators:
% 2.59/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.59/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.59/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.59/1.44  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.59/1.44  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.59/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.59/1.44  tff('#skF_7', type, '#skF_7': $i).
% 2.59/1.44  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.59/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.59/1.44  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.59/1.44  tff('#skF_6', type, '#skF_6': $i).
% 2.59/1.44  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.59/1.44  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.59/1.44  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.59/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.59/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.59/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.59/1.44  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.59/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.59/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.59/1.44  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.59/1.44  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.59/1.44  
% 2.59/1.46  tff(f_81, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 2.59/1.46  tff(f_37, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.59/1.46  tff(f_73, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 2.59/1.46  tff(f_61, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 2.59/1.46  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 2.59/1.46  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 2.59/1.46  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.59/1.46  tff(f_39, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.59/1.46  tff(f_48, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.59/1.46  tff(f_41, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.59/1.46  tff(f_46, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 2.59/1.46  tff(c_38, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.59/1.46  tff(c_40, plain, (k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0 | ~r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.59/1.46  tff(c_157, plain, (~r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_40])).
% 2.59/1.46  tff(c_46, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_7')) | k11_relat_1('#skF_7', '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.59/1.46  tff(c_207, plain, (k11_relat_1('#skF_7', '#skF_6')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_157, c_46])).
% 2.59/1.46  tff(c_6, plain, (![A_3]: (r2_hidden('#skF_1'(A_3), A_3) | k1_xboole_0=A_3)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.59/1.46  tff(c_369, plain, (![A_89, B_90, C_91]: (r2_hidden(k4_tarski(A_89, B_90), C_91) | ~r2_hidden(B_90, k11_relat_1(C_91, A_89)) | ~v1_relat_1(C_91))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.59/1.46  tff(c_20, plain, (![C_31, A_16, D_34]: (r2_hidden(C_31, k1_relat_1(A_16)) | ~r2_hidden(k4_tarski(C_31, D_34), A_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.59/1.46  tff(c_383, plain, (![A_95, C_96, B_97]: (r2_hidden(A_95, k1_relat_1(C_96)) | ~r2_hidden(B_97, k11_relat_1(C_96, A_95)) | ~v1_relat_1(C_96))), inference(resolution, [status(thm)], [c_369, c_20])).
% 2.59/1.46  tff(c_392, plain, (![A_98, C_99]: (r2_hidden(A_98, k1_relat_1(C_99)) | ~v1_relat_1(C_99) | k11_relat_1(C_99, A_98)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_383])).
% 2.59/1.46  tff(c_403, plain, (~v1_relat_1('#skF_7') | k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_392, c_157])).
% 2.59/1.46  tff(c_408, plain, (k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_403])).
% 2.59/1.46  tff(c_410, plain, $false, inference(negUnitSimplification, [status(thm)], [c_207, c_408])).
% 2.59/1.46  tff(c_411, plain, (k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_40])).
% 2.59/1.46  tff(c_16, plain, (![A_13, B_15]: (k9_relat_1(A_13, k1_tarski(B_15))=k11_relat_1(A_13, B_15) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.59/1.46  tff(c_412, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_40])).
% 2.59/1.46  tff(c_619, plain, (![B_133, A_134]: (r1_xboole_0(k1_relat_1(B_133), A_134) | k9_relat_1(B_133, A_134)!=k1_xboole_0 | ~v1_relat_1(B_133))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.59/1.46  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.59/1.46  tff(c_630, plain, (![B_139, A_140]: (k3_xboole_0(k1_relat_1(B_139), A_140)=k1_xboole_0 | k9_relat_1(B_139, A_140)!=k1_xboole_0 | ~v1_relat_1(B_139))), inference(resolution, [status(thm)], [c_619, c_2])).
% 2.59/1.46  tff(c_8, plain, (![B_6, A_5]: (k2_tarski(B_6, A_5)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.59/1.46  tff(c_96, plain, (![A_48, B_49]: (k1_setfam_1(k2_tarski(A_48, B_49))=k3_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.59/1.46  tff(c_131, plain, (![B_51, A_52]: (k1_setfam_1(k2_tarski(B_51, A_52))=k3_xboole_0(A_52, B_51))), inference(superposition, [status(thm), theory('equality')], [c_8, c_96])).
% 2.59/1.46  tff(c_14, plain, (![A_11, B_12]: (k1_setfam_1(k2_tarski(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.59/1.46  tff(c_137, plain, (![B_51, A_52]: (k3_xboole_0(B_51, A_52)=k3_xboole_0(A_52, B_51))), inference(superposition, [status(thm), theory('equality')], [c_131, c_14])).
% 2.59/1.46  tff(c_785, plain, (![A_159, B_160]: (k3_xboole_0(A_159, k1_relat_1(B_160))=k1_xboole_0 | k9_relat_1(B_160, A_159)!=k1_xboole_0 | ~v1_relat_1(B_160))), inference(superposition, [status(thm), theory('equality')], [c_630, c_137])).
% 2.59/1.46  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.59/1.46  tff(c_10, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.59/1.46  tff(c_450, plain, (![A_102, C_103, B_104]: (~r2_hidden(A_102, C_103) | ~r1_xboole_0(k2_tarski(A_102, B_104), C_103))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.59/1.46  tff(c_465, plain, (![A_105, C_106]: (~r2_hidden(A_105, C_106) | ~r1_xboole_0(k1_tarski(A_105), C_106))), inference(superposition, [status(thm), theory('equality')], [c_10, c_450])).
% 2.59/1.46  tff(c_470, plain, (![A_105, B_2]: (~r2_hidden(A_105, B_2) | k3_xboole_0(k1_tarski(A_105), B_2)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_465])).
% 2.59/1.46  tff(c_885, plain, (![A_170, B_171]: (~r2_hidden(A_170, k1_relat_1(B_171)) | k9_relat_1(B_171, k1_tarski(A_170))!=k1_xboole_0 | ~v1_relat_1(B_171))), inference(superposition, [status(thm), theory('equality')], [c_785, c_470])).
% 2.59/1.46  tff(c_899, plain, (k9_relat_1('#skF_7', k1_tarski('#skF_6'))!=k1_xboole_0 | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_412, c_885])).
% 2.59/1.46  tff(c_909, plain, (k9_relat_1('#skF_7', k1_tarski('#skF_6'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_899])).
% 2.59/1.46  tff(c_913, plain, (k11_relat_1('#skF_7', '#skF_6')!=k1_xboole_0 | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_16, c_909])).
% 2.59/1.46  tff(c_916, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_411, c_913])).
% 2.59/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.46  
% 2.59/1.46  Inference rules
% 2.59/1.46  ----------------------
% 2.59/1.46  #Ref     : 0
% 2.59/1.46  #Sup     : 210
% 2.59/1.46  #Fact    : 0
% 2.59/1.46  #Define  : 0
% 2.59/1.46  #Split   : 1
% 2.59/1.46  #Chain   : 0
% 2.59/1.46  #Close   : 0
% 2.59/1.46  
% 2.59/1.46  Ordering : KBO
% 2.59/1.46  
% 2.59/1.46  Simplification rules
% 2.59/1.46  ----------------------
% 2.59/1.46  #Subsume      : 74
% 2.59/1.46  #Demod        : 16
% 2.59/1.46  #Tautology    : 62
% 2.59/1.46  #SimpNegUnit  : 2
% 2.59/1.46  #BackRed      : 0
% 2.59/1.46  
% 2.59/1.46  #Partial instantiations: 0
% 2.59/1.46  #Strategies tried      : 1
% 2.59/1.46  
% 2.59/1.46  Timing (in seconds)
% 2.59/1.46  ----------------------
% 2.59/1.46  Preprocessing        : 0.33
% 2.59/1.46  Parsing              : 0.17
% 2.59/1.46  CNF conversion       : 0.03
% 2.59/1.46  Main loop            : 0.34
% 2.59/1.46  Inferencing          : 0.13
% 2.59/1.46  Reduction            : 0.11
% 2.59/1.46  Demodulation         : 0.09
% 2.59/1.46  BG Simplification    : 0.02
% 2.59/1.46  Subsumption          : 0.06
% 2.59/1.46  Abstraction          : 0.02
% 2.59/1.46  MUC search           : 0.00
% 2.59/1.46  Cooper               : 0.00
% 2.59/1.46  Total                : 0.70
% 2.59/1.46  Index Insertion      : 0.00
% 2.59/1.46  Index Deletion       : 0.00
% 2.59/1.46  Index Matching       : 0.00
% 2.59/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
