%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:28 EST 2020

% Result     : Theorem 3.55s
% Output     : CNFRefutation 3.66s
% Verified   : 
% Statistics : Number of formulae       :   64 (  92 expanded)
%              Number of leaves         :   33 (  49 expanded)
%              Depth                    :   12
%              Number of atoms          :   66 ( 118 expanded)
%              Number of equality atoms :   28 (  49 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_104,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_xboole_0(A,B)
            & v2_funct_1(C) )
         => r1_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_funct_1)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_relat_1)).

tff(f_59,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_61,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_63,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_48,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_46,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_42,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_65,plain,(
    ! [A_52] :
      ( k9_relat_1(A_52,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_69,plain,(
    k9_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_65])).

tff(c_12,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_14,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_110,plain,(
    ! [A_61,B_62] : k4_xboole_0(A_61,k4_xboole_0(A_61,B_62)) = k3_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_128,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k3_xboole_0(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_110])).

tff(c_131,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_128])).

tff(c_44,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_79,plain,(
    ! [A_55,B_56] :
      ( k4_xboole_0(A_55,B_56) = A_55
      | ~ r1_xboole_0(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_87,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_44,c_79])).

tff(c_125,plain,(
    k4_xboole_0('#skF_3','#skF_3') = k3_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_110])).

tff(c_173,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_125])).

tff(c_1516,plain,(
    ! [C_166,A_167,B_168] :
      ( k3_xboole_0(k9_relat_1(C_166,A_167),k9_relat_1(C_166,B_168)) = k9_relat_1(C_166,k3_xboole_0(A_167,B_168))
      | ~ v2_funct_1(C_166)
      | ~ v1_funct_1(C_166)
      | ~ v1_relat_1(C_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_602,plain,(
    ! [A_103,B_104] :
      ( r2_hidden('#skF_2'(A_103,B_104),k3_xboole_0(A_103,B_104))
      | r1_xboole_0(A_103,B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( r1_xboole_0(A_15,B_16)
      | k4_xboole_0(A_15,B_16) != A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_133,plain,(
    ! [A_65] : k4_xboole_0(A_65,A_65) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_128])).

tff(c_16,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_138,plain,(
    ! [A_65] : k4_xboole_0(A_65,k1_xboole_0) = k3_xboole_0(A_65,A_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_16])).

tff(c_150,plain,(
    ! [A_65] : k3_xboole_0(A_65,A_65) = A_65 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_138])).

tff(c_178,plain,(
    ! [A_67,B_68,C_69] :
      ( ~ r1_xboole_0(A_67,B_68)
      | ~ r2_hidden(C_69,k3_xboole_0(A_67,B_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_303,plain,(
    ! [A_80,C_81] :
      ( ~ r1_xboole_0(A_80,A_80)
      | ~ r2_hidden(C_81,A_80) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_178])).

tff(c_312,plain,(
    ! [C_81,B_16] :
      ( ~ r2_hidden(C_81,B_16)
      | k4_xboole_0(B_16,B_16) != B_16 ) ),
    inference(resolution,[status(thm)],[c_20,c_303])).

tff(c_316,plain,(
    ! [C_81,B_16] :
      ( ~ r2_hidden(C_81,B_16)
      | k1_xboole_0 != B_16 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_312])).

tff(c_630,plain,(
    ! [A_105,B_106] :
      ( k3_xboole_0(A_105,B_106) != k1_xboole_0
      | r1_xboole_0(A_105,B_106) ) ),
    inference(resolution,[status(thm)],[c_602,c_316])).

tff(c_40,plain,(
    ~ r1_xboole_0(k9_relat_1('#skF_5','#skF_3'),k9_relat_1('#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_646,plain,(
    k3_xboole_0(k9_relat_1('#skF_5','#skF_3'),k9_relat_1('#skF_5','#skF_4')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_630,c_40])).

tff(c_1537,plain,
    ( k9_relat_1('#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k1_xboole_0
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1516,c_646])).

tff(c_1585,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_42,c_69,c_173,c_1537])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:26:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.55/1.81  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.55/1.81  
% 3.55/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.64/1.82  %$ r2_hidden > r1_xboole_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.64/1.82  
% 3.64/1.82  %Foreground sorts:
% 3.64/1.82  
% 3.64/1.82  
% 3.64/1.82  %Background operators:
% 3.64/1.82  
% 3.64/1.82  
% 3.64/1.82  %Foreground operators:
% 3.64/1.82  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.64/1.82  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.64/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.64/1.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.64/1.82  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.64/1.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.64/1.82  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.64/1.82  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.64/1.82  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.64/1.82  tff('#skF_5', type, '#skF_5': $i).
% 3.64/1.82  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.64/1.82  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.64/1.82  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.64/1.82  tff('#skF_3', type, '#skF_3': $i).
% 3.64/1.82  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.64/1.82  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.64/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.64/1.82  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.64/1.82  tff('#skF_4', type, '#skF_4': $i).
% 3.64/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.64/1.82  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.64/1.82  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.64/1.82  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.64/1.82  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.64/1.82  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.64/1.82  
% 3.66/1.83  tff(f_104, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_xboole_0(A, B) & v2_funct_1(C)) => r1_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_funct_1)).
% 3.66/1.83  tff(f_85, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_relat_1)).
% 3.66/1.83  tff(f_59, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.66/1.83  tff(f_61, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.66/1.83  tff(f_63, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.66/1.83  tff(f_67, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.66/1.83  tff(f_93, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_funct_1)).
% 3.66/1.83  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.66/1.83  tff(c_48, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.66/1.83  tff(c_46, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.66/1.83  tff(c_42, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.66/1.83  tff(c_65, plain, (![A_52]: (k9_relat_1(A_52, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.66/1.83  tff(c_69, plain, (k9_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_48, c_65])).
% 3.66/1.83  tff(c_12, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.66/1.83  tff(c_14, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.66/1.83  tff(c_110, plain, (![A_61, B_62]: (k4_xboole_0(A_61, k4_xboole_0(A_61, B_62))=k3_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.66/1.83  tff(c_128, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k3_xboole_0(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_110])).
% 3.66/1.83  tff(c_131, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_128])).
% 3.66/1.83  tff(c_44, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.66/1.83  tff(c_79, plain, (![A_55, B_56]: (k4_xboole_0(A_55, B_56)=A_55 | ~r1_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.66/1.83  tff(c_87, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_44, c_79])).
% 3.66/1.83  tff(c_125, plain, (k4_xboole_0('#skF_3', '#skF_3')=k3_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_87, c_110])).
% 3.66/1.83  tff(c_173, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_131, c_125])).
% 3.66/1.83  tff(c_1516, plain, (![C_166, A_167, B_168]: (k3_xboole_0(k9_relat_1(C_166, A_167), k9_relat_1(C_166, B_168))=k9_relat_1(C_166, k3_xboole_0(A_167, B_168)) | ~v2_funct_1(C_166) | ~v1_funct_1(C_166) | ~v1_relat_1(C_166))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.66/1.83  tff(c_602, plain, (![A_103, B_104]: (r2_hidden('#skF_2'(A_103, B_104), k3_xboole_0(A_103, B_104)) | r1_xboole_0(A_103, B_104))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.66/1.83  tff(c_20, plain, (![A_15, B_16]: (r1_xboole_0(A_15, B_16) | k4_xboole_0(A_15, B_16)!=A_15)), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.66/1.83  tff(c_133, plain, (![A_65]: (k4_xboole_0(A_65, A_65)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_128])).
% 3.66/1.83  tff(c_16, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.66/1.83  tff(c_138, plain, (![A_65]: (k4_xboole_0(A_65, k1_xboole_0)=k3_xboole_0(A_65, A_65))), inference(superposition, [status(thm), theory('equality')], [c_133, c_16])).
% 3.66/1.83  tff(c_150, plain, (![A_65]: (k3_xboole_0(A_65, A_65)=A_65)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_138])).
% 3.66/1.83  tff(c_178, plain, (![A_67, B_68, C_69]: (~r1_xboole_0(A_67, B_68) | ~r2_hidden(C_69, k3_xboole_0(A_67, B_68)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.66/1.83  tff(c_303, plain, (![A_80, C_81]: (~r1_xboole_0(A_80, A_80) | ~r2_hidden(C_81, A_80))), inference(superposition, [status(thm), theory('equality')], [c_150, c_178])).
% 3.66/1.83  tff(c_312, plain, (![C_81, B_16]: (~r2_hidden(C_81, B_16) | k4_xboole_0(B_16, B_16)!=B_16)), inference(resolution, [status(thm)], [c_20, c_303])).
% 3.66/1.83  tff(c_316, plain, (![C_81, B_16]: (~r2_hidden(C_81, B_16) | k1_xboole_0!=B_16)), inference(demodulation, [status(thm), theory('equality')], [c_131, c_312])).
% 3.66/1.83  tff(c_630, plain, (![A_105, B_106]: (k3_xboole_0(A_105, B_106)!=k1_xboole_0 | r1_xboole_0(A_105, B_106))), inference(resolution, [status(thm)], [c_602, c_316])).
% 3.66/1.83  tff(c_40, plain, (~r1_xboole_0(k9_relat_1('#skF_5', '#skF_3'), k9_relat_1('#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.66/1.83  tff(c_646, plain, (k3_xboole_0(k9_relat_1('#skF_5', '#skF_3'), k9_relat_1('#skF_5', '#skF_4'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_630, c_40])).
% 3.66/1.83  tff(c_1537, plain, (k9_relat_1('#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k1_xboole_0 | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1516, c_646])).
% 3.66/1.83  tff(c_1585, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_42, c_69, c_173, c_1537])).
% 3.66/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.66/1.83  
% 3.66/1.83  Inference rules
% 3.66/1.83  ----------------------
% 3.66/1.83  #Ref     : 0
% 3.66/1.83  #Sup     : 375
% 3.66/1.83  #Fact    : 0
% 3.66/1.83  #Define  : 0
% 3.66/1.83  #Split   : 1
% 3.66/1.83  #Chain   : 0
% 3.66/1.83  #Close   : 0
% 3.66/1.83  
% 3.66/1.83  Ordering : KBO
% 3.66/1.83  
% 3.66/1.83  Simplification rules
% 3.66/1.83  ----------------------
% 3.66/1.83  #Subsume      : 92
% 3.66/1.83  #Demod        : 113
% 3.66/1.83  #Tautology    : 202
% 3.66/1.83  #SimpNegUnit  : 6
% 3.66/1.83  #BackRed      : 0
% 3.66/1.83  
% 3.66/1.83  #Partial instantiations: 0
% 3.66/1.83  #Strategies tried      : 1
% 3.66/1.83  
% 3.66/1.83  Timing (in seconds)
% 3.66/1.83  ----------------------
% 3.66/1.83  Preprocessing        : 0.51
% 3.66/1.83  Parsing              : 0.30
% 3.66/1.83  CNF conversion       : 0.03
% 3.66/1.83  Main loop            : 0.47
% 3.66/1.83  Inferencing          : 0.19
% 3.66/1.83  Reduction            : 0.14
% 3.66/1.83  Demodulation         : 0.10
% 3.66/1.83  BG Simplification    : 0.03
% 3.66/1.83  Subsumption          : 0.09
% 3.66/1.83  Abstraction          : 0.03
% 3.66/1.83  MUC search           : 0.00
% 3.66/1.83  Cooper               : 0.00
% 3.66/1.83  Total                : 1.01
% 3.66/1.83  Index Insertion      : 0.00
% 3.66/1.83  Index Deletion       : 0.00
% 3.66/1.83  Index Matching       : 0.00
% 3.66/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
