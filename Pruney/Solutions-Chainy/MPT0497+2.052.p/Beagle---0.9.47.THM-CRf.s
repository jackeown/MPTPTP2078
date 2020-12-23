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
% DateTime   : Thu Dec  3 09:59:46 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 170 expanded)
%              Number of leaves         :   30 (  69 expanded)
%              Depth                    :   13
%              Number of atoms          :   91 ( 234 expanded)
%              Number of equality atoms :   49 ( 133 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k7_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_73,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_44,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_36,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_46,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2')
    | k7_relat_1('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_107,plain,(
    k7_relat_1('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_446,plain,(
    ! [B_77,A_78] :
      ( k3_xboole_0(k1_relat_1(B_77),A_78) = k1_relat_1(k7_relat_1(B_77,A_78))
      | ~ v1_relat_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_6,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_190,plain,(
    ! [A_56,B_57] : k4_xboole_0(A_56,k4_xboole_0(A_56,B_57)) = k3_xboole_0(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_211,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k3_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_190])).

tff(c_217,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_211])).

tff(c_52,plain,
    ( k7_relat_1('#skF_3','#skF_2') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_129,plain,(
    r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_52])).

tff(c_131,plain,(
    ! [A_43,B_44] :
      ( k4_xboole_0(A_43,B_44) = A_43
      | ~ r1_xboole_0(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_139,plain,(
    k4_xboole_0(k1_relat_1('#skF_3'),'#skF_2') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_129,c_131])).

tff(c_208,plain,(
    k4_xboole_0(k1_relat_1('#skF_3'),k1_relat_1('#skF_3')) = k3_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_190])).

tff(c_226,plain,(
    k3_xboole_0(k1_relat_1('#skF_3'),'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_208])).

tff(c_466,plain,
    ( k1_relat_1(k7_relat_1('#skF_3','#skF_2')) = k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_446,c_226])).

tff(c_508,plain,(
    k1_relat_1(k7_relat_1('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_466])).

tff(c_32,plain,(
    ! [A_25,B_26] :
      ( v1_relat_1(k7_relat_1(A_25,B_26))
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_42,plain,(
    ! [B_29,A_28] :
      ( k3_xboole_0(k1_relat_1(B_29),A_28) = k1_relat_1(k7_relat_1(B_29,A_28))
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_515,plain,(
    ! [A_28] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_3','#skF_2'),A_28)) = k3_xboole_0(k1_xboole_0,A_28)
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_508,c_42])).

tff(c_530,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_515])).

tff(c_533,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_530])).

tff(c_537,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_533])).

tff(c_539,plain,(
    v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_515])).

tff(c_40,plain,(
    ! [A_27] :
      ( k1_relat_1(A_27) != k1_xboole_0
      | k1_xboole_0 = A_27
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_542,plain,
    ( k1_relat_1(k7_relat_1('#skF_3','#skF_2')) != k1_xboole_0
    | k7_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_539,c_40])).

tff(c_548,plain,(
    k7_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_508,c_542])).

tff(c_550,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_548])).

tff(c_552,plain,(
    k7_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_843,plain,(
    ! [B_119,A_120] :
      ( k3_xboole_0(k1_relat_1(B_119),A_120) = k1_relat_1(k7_relat_1(B_119,A_120))
      | ~ v1_relat_1(B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_774,plain,(
    ! [A_112,B_113] :
      ( r2_hidden('#skF_1'(A_112,B_113),k3_xboole_0(A_112,B_113))
      | r1_xboole_0(A_112,B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_642,plain,(
    ! [A_97,B_98] : k4_xboole_0(A_97,k4_xboole_0(A_97,B_98)) = k3_xboole_0(A_97,B_98) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_657,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k3_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_642])).

tff(c_660,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_657])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( r1_xboole_0(A_12,B_13)
      | k4_xboole_0(A_12,B_13) != A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_661,plain,(
    ! [A_99] : k4_xboole_0(A_99,A_99) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_657])).

tff(c_12,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_666,plain,(
    ! [A_99] : k4_xboole_0(A_99,k1_xboole_0) = k3_xboole_0(A_99,A_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_661,c_12])).

tff(c_682,plain,(
    ! [A_100] : k3_xboole_0(A_100,A_100) = A_100 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_666])).

tff(c_4,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_704,plain,(
    ! [A_101,C_102] :
      ( ~ r1_xboole_0(A_101,A_101)
      | ~ r2_hidden(C_102,A_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_682,c_4])).

tff(c_707,plain,(
    ! [C_102,B_13] :
      ( ~ r2_hidden(C_102,B_13)
      | k4_xboole_0(B_13,B_13) != B_13 ) ),
    inference(resolution,[status(thm)],[c_16,c_704])).

tff(c_709,plain,(
    ! [C_102,B_13] :
      ( ~ r2_hidden(C_102,B_13)
      | k1_xboole_0 != B_13 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_660,c_707])).

tff(c_803,plain,(
    ! [A_115,B_116] :
      ( k3_xboole_0(A_115,B_116) != k1_xboole_0
      | r1_xboole_0(A_115,B_116) ) ),
    inference(resolution,[status(thm)],[c_774,c_709])).

tff(c_551,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_816,plain,(
    k3_xboole_0(k1_relat_1('#skF_3'),'#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_803,c_551])).

tff(c_849,plain,
    ( k1_relat_1(k7_relat_1('#skF_3','#skF_2')) != k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_843,c_816])).

tff(c_895,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_36,c_552,c_849])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:18:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.61/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.40  
% 2.61/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.40  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.61/1.40  
% 2.61/1.40  %Foreground sorts:
% 2.61/1.40  
% 2.61/1.40  
% 2.61/1.40  %Background operators:
% 2.61/1.40  
% 2.61/1.40  
% 2.61/1.40  %Foreground operators:
% 2.61/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.61/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.61/1.40  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.61/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.61/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.61/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.61/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.61/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.61/1.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.61/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.61/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.61/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.61/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.61/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.61/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.61/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.61/1.40  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.61/1.40  
% 2.61/1.41  tff(f_92, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 2.61/1.41  tff(f_73, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.61/1.41  tff(f_85, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 2.61/1.41  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.61/1.41  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.61/1.41  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.61/1.41  tff(f_51, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.61/1.41  tff(f_70, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.61/1.41  tff(f_81, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 2.61/1.41  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.61/1.41  tff(c_44, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.61/1.41  tff(c_36, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.61/1.41  tff(c_46, plain, (~r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2') | k7_relat_1('#skF_3', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.61/1.41  tff(c_107, plain, (k7_relat_1('#skF_3', '#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_46])).
% 2.61/1.41  tff(c_446, plain, (![B_77, A_78]: (k3_xboole_0(k1_relat_1(B_77), A_78)=k1_relat_1(k7_relat_1(B_77, A_78)) | ~v1_relat_1(B_77))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.61/1.41  tff(c_6, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.61/1.41  tff(c_8, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.61/1.41  tff(c_190, plain, (![A_56, B_57]: (k4_xboole_0(A_56, k4_xboole_0(A_56, B_57))=k3_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.61/1.41  tff(c_211, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k3_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_190])).
% 2.61/1.41  tff(c_217, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_211])).
% 2.61/1.41  tff(c_52, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.61/1.41  tff(c_129, plain, (r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_107, c_52])).
% 2.61/1.41  tff(c_131, plain, (![A_43, B_44]: (k4_xboole_0(A_43, B_44)=A_43 | ~r1_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.61/1.41  tff(c_139, plain, (k4_xboole_0(k1_relat_1('#skF_3'), '#skF_2')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_129, c_131])).
% 2.61/1.41  tff(c_208, plain, (k4_xboole_0(k1_relat_1('#skF_3'), k1_relat_1('#skF_3'))=k3_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_139, c_190])).
% 2.61/1.41  tff(c_226, plain, (k3_xboole_0(k1_relat_1('#skF_3'), '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_217, c_208])).
% 2.61/1.41  tff(c_466, plain, (k1_relat_1(k7_relat_1('#skF_3', '#skF_2'))=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_446, c_226])).
% 2.61/1.41  tff(c_508, plain, (k1_relat_1(k7_relat_1('#skF_3', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_44, c_466])).
% 2.61/1.41  tff(c_32, plain, (![A_25, B_26]: (v1_relat_1(k7_relat_1(A_25, B_26)) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.61/1.41  tff(c_42, plain, (![B_29, A_28]: (k3_xboole_0(k1_relat_1(B_29), A_28)=k1_relat_1(k7_relat_1(B_29, A_28)) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.61/1.41  tff(c_515, plain, (![A_28]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_3', '#skF_2'), A_28))=k3_xboole_0(k1_xboole_0, A_28) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_508, c_42])).
% 2.61/1.41  tff(c_530, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_515])).
% 2.61/1.41  tff(c_533, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_530])).
% 2.61/1.41  tff(c_537, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_533])).
% 2.61/1.41  tff(c_539, plain, (v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_515])).
% 2.61/1.41  tff(c_40, plain, (![A_27]: (k1_relat_1(A_27)!=k1_xboole_0 | k1_xboole_0=A_27 | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.61/1.41  tff(c_542, plain, (k1_relat_1(k7_relat_1('#skF_3', '#skF_2'))!=k1_xboole_0 | k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_539, c_40])).
% 2.61/1.41  tff(c_548, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_508, c_542])).
% 2.61/1.41  tff(c_550, plain, $false, inference(negUnitSimplification, [status(thm)], [c_107, c_548])).
% 2.61/1.41  tff(c_552, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_46])).
% 2.61/1.41  tff(c_843, plain, (![B_119, A_120]: (k3_xboole_0(k1_relat_1(B_119), A_120)=k1_relat_1(k7_relat_1(B_119, A_120)) | ~v1_relat_1(B_119))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.61/1.41  tff(c_774, plain, (![A_112, B_113]: (r2_hidden('#skF_1'(A_112, B_113), k3_xboole_0(A_112, B_113)) | r1_xboole_0(A_112, B_113))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.61/1.41  tff(c_642, plain, (![A_97, B_98]: (k4_xboole_0(A_97, k4_xboole_0(A_97, B_98))=k3_xboole_0(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.61/1.41  tff(c_657, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k3_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_642])).
% 2.61/1.41  tff(c_660, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_657])).
% 2.61/1.41  tff(c_16, plain, (![A_12, B_13]: (r1_xboole_0(A_12, B_13) | k4_xboole_0(A_12, B_13)!=A_12)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.61/1.41  tff(c_661, plain, (![A_99]: (k4_xboole_0(A_99, A_99)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_657])).
% 2.61/1.41  tff(c_12, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.61/1.41  tff(c_666, plain, (![A_99]: (k4_xboole_0(A_99, k1_xboole_0)=k3_xboole_0(A_99, A_99))), inference(superposition, [status(thm), theory('equality')], [c_661, c_12])).
% 2.61/1.41  tff(c_682, plain, (![A_100]: (k3_xboole_0(A_100, A_100)=A_100)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_666])).
% 2.61/1.41  tff(c_4, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.61/1.41  tff(c_704, plain, (![A_101, C_102]: (~r1_xboole_0(A_101, A_101) | ~r2_hidden(C_102, A_101))), inference(superposition, [status(thm), theory('equality')], [c_682, c_4])).
% 2.61/1.41  tff(c_707, plain, (![C_102, B_13]: (~r2_hidden(C_102, B_13) | k4_xboole_0(B_13, B_13)!=B_13)), inference(resolution, [status(thm)], [c_16, c_704])).
% 2.61/1.41  tff(c_709, plain, (![C_102, B_13]: (~r2_hidden(C_102, B_13) | k1_xboole_0!=B_13)), inference(demodulation, [status(thm), theory('equality')], [c_660, c_707])).
% 2.61/1.41  tff(c_803, plain, (![A_115, B_116]: (k3_xboole_0(A_115, B_116)!=k1_xboole_0 | r1_xboole_0(A_115, B_116))), inference(resolution, [status(thm)], [c_774, c_709])).
% 2.61/1.41  tff(c_551, plain, (~r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_46])).
% 2.61/1.41  tff(c_816, plain, (k3_xboole_0(k1_relat_1('#skF_3'), '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_803, c_551])).
% 2.61/1.41  tff(c_849, plain, (k1_relat_1(k7_relat_1('#skF_3', '#skF_2'))!=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_843, c_816])).
% 2.61/1.41  tff(c_895, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_36, c_552, c_849])).
% 2.61/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.41  
% 2.61/1.41  Inference rules
% 2.61/1.41  ----------------------
% 2.61/1.41  #Ref     : 0
% 2.61/1.41  #Sup     : 198
% 2.61/1.41  #Fact    : 0
% 2.61/1.41  #Define  : 0
% 2.61/1.41  #Split   : 6
% 2.61/1.41  #Chain   : 0
% 2.61/1.41  #Close   : 0
% 2.61/1.41  
% 2.61/1.41  Ordering : KBO
% 2.61/1.41  
% 2.61/1.41  Simplification rules
% 2.61/1.41  ----------------------
% 2.61/1.41  #Subsume      : 11
% 2.61/1.41  #Demod        : 83
% 2.61/1.41  #Tautology    : 115
% 2.61/1.41  #SimpNegUnit  : 6
% 2.61/1.41  #BackRed      : 1
% 2.61/1.41  
% 2.61/1.41  #Partial instantiations: 0
% 2.61/1.41  #Strategies tried      : 1
% 2.61/1.41  
% 2.61/1.41  Timing (in seconds)
% 2.61/1.41  ----------------------
% 2.61/1.42  Preprocessing        : 0.32
% 2.61/1.42  Parsing              : 0.17
% 2.61/1.42  CNF conversion       : 0.02
% 2.61/1.42  Main loop            : 0.30
% 2.61/1.42  Inferencing          : 0.12
% 2.61/1.42  Reduction            : 0.09
% 2.61/1.42  Demodulation         : 0.06
% 2.61/1.42  BG Simplification    : 0.02
% 2.61/1.42  Subsumption          : 0.04
% 2.61/1.42  Abstraction          : 0.02
% 2.87/1.42  MUC search           : 0.00
% 2.87/1.42  Cooper               : 0.00
% 2.87/1.42  Total                : 0.65
% 2.87/1.42  Index Insertion      : 0.00
% 2.87/1.42  Index Deletion       : 0.00
% 2.87/1.42  Index Matching       : 0.00
% 2.87/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
