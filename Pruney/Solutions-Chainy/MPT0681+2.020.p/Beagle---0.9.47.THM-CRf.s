%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:28 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :   63 (  77 expanded)
%              Number of leaves         :   35 (  45 expanded)
%              Depth                    :    7
%              Number of atoms          :   91 ( 156 expanded)
%              Number of equality atoms :   18 (  18 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_104,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_xboole_0(A,B)
            & v2_funct_1(C) )
         => r1_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_funct_1)).

tff(f_61,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_85,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_1)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_44,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_135,plain,(
    ! [A_77,B_78,C_79] :
      ( ~ r1_xboole_0(A_77,B_78)
      | ~ r2_hidden(C_79,B_78)
      | ~ r2_hidden(C_79,A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_148,plain,(
    ! [C_80] :
      ( ~ r2_hidden(C_80,'#skF_4')
      | ~ r2_hidden(C_80,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_44,c_135])).

tff(c_166,plain,(
    ! [A_82] :
      ( ~ r2_hidden('#skF_1'(A_82,'#skF_3'),'#skF_4')
      | r1_xboole_0(A_82,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_4,c_148])).

tff(c_171,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_166])).

tff(c_48,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_46,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_42,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_14,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_105,plain,(
    ! [A_65,B_66,C_67] :
      ( ~ r1_xboole_0(A_65,B_66)
      | ~ r2_hidden(C_67,k3_xboole_0(A_65,B_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_115,plain,(
    ! [A_65,B_66,A_1] :
      ( ~ r1_xboole_0(A_65,B_66)
      | r1_xboole_0(A_1,k3_xboole_0(A_65,B_66)) ) ),
    inference(resolution,[status(thm)],[c_4,c_105])).

tff(c_205,plain,(
    ! [B_90,A_91] :
      ( k9_relat_1(B_90,A_91) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_90),A_91)
      | ~ v1_relat_1(B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_218,plain,(
    ! [B_90,A_65,B_66] :
      ( k9_relat_1(B_90,k3_xboole_0(A_65,B_66)) = k1_xboole_0
      | ~ v1_relat_1(B_90)
      | ~ r1_xboole_0(A_65,B_66) ) ),
    inference(resolution,[status(thm)],[c_115,c_205])).

tff(c_507,plain,(
    ! [C_164,A_165,B_166] :
      ( k3_xboole_0(k9_relat_1(C_164,A_165),k9_relat_1(C_164,B_166)) = k9_relat_1(C_164,k3_xboole_0(A_165,B_166))
      | ~ v2_funct_1(C_164)
      | ~ v1_funct_1(C_164)
      | ~ v1_relat_1(C_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_12,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_688,plain,(
    ! [C_210,A_211,B_212] :
      ( k5_xboole_0(k9_relat_1(C_210,A_211),k9_relat_1(C_210,k3_xboole_0(A_211,B_212))) = k4_xboole_0(k9_relat_1(C_210,A_211),k9_relat_1(C_210,B_212))
      | ~ v2_funct_1(C_210)
      | ~ v1_funct_1(C_210)
      | ~ v1_relat_1(C_210) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_507,c_12])).

tff(c_703,plain,(
    ! [B_90,A_65,B_66] :
      ( k4_xboole_0(k9_relat_1(B_90,A_65),k9_relat_1(B_90,B_66)) = k5_xboole_0(k9_relat_1(B_90,A_65),k1_xboole_0)
      | ~ v2_funct_1(B_90)
      | ~ v1_funct_1(B_90)
      | ~ v1_relat_1(B_90)
      | ~ v1_relat_1(B_90)
      | ~ r1_xboole_0(A_65,B_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_688])).

tff(c_707,plain,(
    ! [B_213,A_214,B_215] :
      ( k4_xboole_0(k9_relat_1(B_213,A_214),k9_relat_1(B_213,B_215)) = k9_relat_1(B_213,A_214)
      | ~ v2_funct_1(B_213)
      | ~ v1_funct_1(B_213)
      | ~ v1_relat_1(B_213)
      | ~ v1_relat_1(B_213)
      | ~ r1_xboole_0(A_214,B_215) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_703])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( r1_xboole_0(A_14,B_15)
      | k4_xboole_0(A_14,B_15) != A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_229,plain,(
    ! [C_96,B_97,A_98] :
      ( ~ r2_hidden(C_96,B_97)
      | ~ r2_hidden(C_96,A_98)
      | k4_xboole_0(A_98,B_97) != A_98 ) ),
    inference(resolution,[status(thm)],[c_18,c_135])).

tff(c_305,plain,(
    ! [A_114,B_115,A_116] :
      ( ~ r2_hidden('#skF_1'(A_114,B_115),A_116)
      | k4_xboole_0(A_116,A_114) != A_116
      | r1_xboole_0(A_114,B_115) ) ),
    inference(resolution,[status(thm)],[c_6,c_229])).

tff(c_327,plain,(
    ! [B_119,A_120] :
      ( k4_xboole_0(B_119,A_120) != B_119
      | r1_xboole_0(A_120,B_119) ) ),
    inference(resolution,[status(thm)],[c_4,c_305])).

tff(c_40,plain,(
    ~ r1_xboole_0(k9_relat_1('#skF_5','#skF_3'),k9_relat_1('#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_343,plain,(
    k4_xboole_0(k9_relat_1('#skF_5','#skF_4'),k9_relat_1('#skF_5','#skF_3')) != k9_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_327,c_40])).

tff(c_718,plain,
    ( ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ r1_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_707,c_343])).

tff(c_740,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_48,c_46,c_42,c_718])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:54:25 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.32/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/1.51  
% 3.32/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/1.51  %$ r2_hidden > r1_xboole_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.32/1.51  
% 3.32/1.51  %Foreground sorts:
% 3.32/1.51  
% 3.32/1.51  
% 3.32/1.51  %Background operators:
% 3.32/1.51  
% 3.32/1.51  
% 3.32/1.51  %Foreground operators:
% 3.32/1.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.32/1.51  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.32/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.32/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.32/1.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.32/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.32/1.51  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.32/1.51  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.32/1.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.32/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.32/1.51  tff('#skF_5', type, '#skF_5': $i).
% 3.32/1.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.32/1.51  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.32/1.51  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.32/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.32/1.51  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.32/1.51  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.32/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.32/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.32/1.51  tff('#skF_4', type, '#skF_4': $i).
% 3.32/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.32/1.51  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.32/1.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.32/1.51  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.32/1.51  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.32/1.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.32/1.51  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.32/1.51  
% 3.40/1.53  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.40/1.53  tff(f_104, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_xboole_0(A, B) & v2_funct_1(C)) => r1_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_funct_1)).
% 3.40/1.53  tff(f_61, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.40/1.53  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.40/1.53  tff(f_85, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 3.40/1.53  tff(f_93, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_funct_1)).
% 3.40/1.53  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.40/1.53  tff(f_65, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.40/1.53  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.40/1.53  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.40/1.53  tff(c_44, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.40/1.53  tff(c_135, plain, (![A_77, B_78, C_79]: (~r1_xboole_0(A_77, B_78) | ~r2_hidden(C_79, B_78) | ~r2_hidden(C_79, A_77))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.40/1.53  tff(c_148, plain, (![C_80]: (~r2_hidden(C_80, '#skF_4') | ~r2_hidden(C_80, '#skF_3'))), inference(resolution, [status(thm)], [c_44, c_135])).
% 3.40/1.53  tff(c_166, plain, (![A_82]: (~r2_hidden('#skF_1'(A_82, '#skF_3'), '#skF_4') | r1_xboole_0(A_82, '#skF_3'))), inference(resolution, [status(thm)], [c_4, c_148])).
% 3.40/1.53  tff(c_171, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_6, c_166])).
% 3.40/1.53  tff(c_48, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.40/1.53  tff(c_46, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.40/1.53  tff(c_42, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.40/1.53  tff(c_14, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.40/1.53  tff(c_105, plain, (![A_65, B_66, C_67]: (~r1_xboole_0(A_65, B_66) | ~r2_hidden(C_67, k3_xboole_0(A_65, B_66)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.40/1.53  tff(c_115, plain, (![A_65, B_66, A_1]: (~r1_xboole_0(A_65, B_66) | r1_xboole_0(A_1, k3_xboole_0(A_65, B_66)))), inference(resolution, [status(thm)], [c_4, c_105])).
% 3.40/1.53  tff(c_205, plain, (![B_90, A_91]: (k9_relat_1(B_90, A_91)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_90), A_91) | ~v1_relat_1(B_90))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.40/1.53  tff(c_218, plain, (![B_90, A_65, B_66]: (k9_relat_1(B_90, k3_xboole_0(A_65, B_66))=k1_xboole_0 | ~v1_relat_1(B_90) | ~r1_xboole_0(A_65, B_66))), inference(resolution, [status(thm)], [c_115, c_205])).
% 3.40/1.53  tff(c_507, plain, (![C_164, A_165, B_166]: (k3_xboole_0(k9_relat_1(C_164, A_165), k9_relat_1(C_164, B_166))=k9_relat_1(C_164, k3_xboole_0(A_165, B_166)) | ~v2_funct_1(C_164) | ~v1_funct_1(C_164) | ~v1_relat_1(C_164))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.40/1.53  tff(c_12, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.40/1.53  tff(c_688, plain, (![C_210, A_211, B_212]: (k5_xboole_0(k9_relat_1(C_210, A_211), k9_relat_1(C_210, k3_xboole_0(A_211, B_212)))=k4_xboole_0(k9_relat_1(C_210, A_211), k9_relat_1(C_210, B_212)) | ~v2_funct_1(C_210) | ~v1_funct_1(C_210) | ~v1_relat_1(C_210))), inference(superposition, [status(thm), theory('equality')], [c_507, c_12])).
% 3.40/1.53  tff(c_703, plain, (![B_90, A_65, B_66]: (k4_xboole_0(k9_relat_1(B_90, A_65), k9_relat_1(B_90, B_66))=k5_xboole_0(k9_relat_1(B_90, A_65), k1_xboole_0) | ~v2_funct_1(B_90) | ~v1_funct_1(B_90) | ~v1_relat_1(B_90) | ~v1_relat_1(B_90) | ~r1_xboole_0(A_65, B_66))), inference(superposition, [status(thm), theory('equality')], [c_218, c_688])).
% 3.40/1.53  tff(c_707, plain, (![B_213, A_214, B_215]: (k4_xboole_0(k9_relat_1(B_213, A_214), k9_relat_1(B_213, B_215))=k9_relat_1(B_213, A_214) | ~v2_funct_1(B_213) | ~v1_funct_1(B_213) | ~v1_relat_1(B_213) | ~v1_relat_1(B_213) | ~r1_xboole_0(A_214, B_215))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_703])).
% 3.40/1.53  tff(c_18, plain, (![A_14, B_15]: (r1_xboole_0(A_14, B_15) | k4_xboole_0(A_14, B_15)!=A_14)), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.40/1.53  tff(c_229, plain, (![C_96, B_97, A_98]: (~r2_hidden(C_96, B_97) | ~r2_hidden(C_96, A_98) | k4_xboole_0(A_98, B_97)!=A_98)), inference(resolution, [status(thm)], [c_18, c_135])).
% 3.40/1.53  tff(c_305, plain, (![A_114, B_115, A_116]: (~r2_hidden('#skF_1'(A_114, B_115), A_116) | k4_xboole_0(A_116, A_114)!=A_116 | r1_xboole_0(A_114, B_115))), inference(resolution, [status(thm)], [c_6, c_229])).
% 3.40/1.53  tff(c_327, plain, (![B_119, A_120]: (k4_xboole_0(B_119, A_120)!=B_119 | r1_xboole_0(A_120, B_119))), inference(resolution, [status(thm)], [c_4, c_305])).
% 3.40/1.53  tff(c_40, plain, (~r1_xboole_0(k9_relat_1('#skF_5', '#skF_3'), k9_relat_1('#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.40/1.53  tff(c_343, plain, (k4_xboole_0(k9_relat_1('#skF_5', '#skF_4'), k9_relat_1('#skF_5', '#skF_3'))!=k9_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_327, c_40])).
% 3.40/1.53  tff(c_718, plain, (~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~r1_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_707, c_343])).
% 3.40/1.53  tff(c_740, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_171, c_48, c_46, c_42, c_718])).
% 3.40/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.53  
% 3.40/1.53  Inference rules
% 3.40/1.53  ----------------------
% 3.40/1.53  #Ref     : 0
% 3.40/1.53  #Sup     : 165
% 3.40/1.53  #Fact    : 0
% 3.40/1.53  #Define  : 0
% 3.40/1.53  #Split   : 0
% 3.40/1.53  #Chain   : 0
% 3.40/1.53  #Close   : 0
% 3.40/1.53  
% 3.40/1.53  Ordering : KBO
% 3.40/1.53  
% 3.40/1.53  Simplification rules
% 3.40/1.53  ----------------------
% 3.40/1.53  #Subsume      : 31
% 3.40/1.53  #Demod        : 8
% 3.40/1.53  #Tautology    : 55
% 3.40/1.53  #SimpNegUnit  : 0
% 3.40/1.53  #BackRed      : 0
% 3.40/1.53  
% 3.40/1.53  #Partial instantiations: 0
% 3.40/1.53  #Strategies tried      : 1
% 3.40/1.53  
% 3.40/1.53  Timing (in seconds)
% 3.40/1.53  ----------------------
% 3.41/1.53  Preprocessing        : 0.33
% 3.41/1.53  Parsing              : 0.18
% 3.41/1.53  CNF conversion       : 0.02
% 3.41/1.53  Main loop            : 0.43
% 3.41/1.53  Inferencing          : 0.18
% 3.41/1.53  Reduction            : 0.10
% 3.41/1.53  Demodulation         : 0.07
% 3.41/1.53  BG Simplification    : 0.03
% 3.41/1.53  Subsumption          : 0.10
% 3.41/1.53  Abstraction          : 0.02
% 3.41/1.53  MUC search           : 0.00
% 3.41/1.53  Cooper               : 0.00
% 3.41/1.53  Total                : 0.79
% 3.41/1.53  Index Insertion      : 0.00
% 3.41/1.53  Index Deletion       : 0.00
% 3.41/1.53  Index Matching       : 0.00
% 3.41/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
