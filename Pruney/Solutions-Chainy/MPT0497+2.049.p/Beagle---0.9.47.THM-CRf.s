%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:45 EST 2020

% Result     : Theorem 3.01s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :   68 (  92 expanded)
%              Number of leaves         :   29 (  43 expanded)
%              Depth                    :   11
%              Number of atoms          :  106 ( 170 expanded)
%              Number of equality atoms :   27 (  43 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_107,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k7_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

tff(f_47,axiom,(
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

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_92,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_73,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_71,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_84,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_42,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_5'),'#skF_4')
    | k7_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_76,plain,(
    k7_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_40,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_14,plain,(
    ! [A_13] :
      ( r2_hidden('#skF_3'(A_13),A_13)
      | k1_xboole_0 = A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_489,plain,(
    ! [A_72,B_73,C_74] :
      ( r2_hidden(A_72,B_73)
      | ~ r2_hidden(A_72,k1_relat_1(k7_relat_1(C_74,B_73)))
      | ~ v1_relat_1(C_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_504,plain,(
    ! [C_74,B_73] :
      ( r2_hidden('#skF_3'(k1_relat_1(k7_relat_1(C_74,B_73))),B_73)
      | ~ v1_relat_1(C_74)
      | k1_relat_1(k7_relat_1(C_74,B_73)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14,c_489])).

tff(c_507,plain,(
    ! [A_79,C_80,B_81] :
      ( r2_hidden(A_79,k1_relat_1(C_80))
      | ~ r2_hidden(A_79,k1_relat_1(k7_relat_1(C_80,B_81)))
      | ~ v1_relat_1(C_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_898,plain,(
    ! [C_97,B_98] :
      ( r2_hidden('#skF_3'(k1_relat_1(k7_relat_1(C_97,B_98))),k1_relat_1(C_97))
      | ~ v1_relat_1(C_97)
      | k1_relat_1(k7_relat_1(C_97,B_98)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14,c_507])).

tff(c_48,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_115,plain,(
    r1_xboole_0(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_48])).

tff(c_221,plain,(
    ! [A_52,B_53,C_54] :
      ( ~ r1_xboole_0(A_52,B_53)
      | ~ r2_hidden(C_54,B_53)
      | ~ r2_hidden(C_54,A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_231,plain,(
    ! [C_54] :
      ( ~ r2_hidden(C_54,'#skF_4')
      | ~ r2_hidden(C_54,k1_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_115,c_221])).

tff(c_910,plain,(
    ! [B_98] :
      ( ~ r2_hidden('#skF_3'(k1_relat_1(k7_relat_1('#skF_5',B_98))),'#skF_4')
      | ~ v1_relat_1('#skF_5')
      | k1_relat_1(k7_relat_1('#skF_5',B_98)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_898,c_231])).

tff(c_1130,plain,(
    ! [B_102] :
      ( ~ r2_hidden('#skF_3'(k1_relat_1(k7_relat_1('#skF_5',B_102))),'#skF_4')
      | k1_relat_1(k7_relat_1('#skF_5',B_102)) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_910])).

tff(c_1149,plain,
    ( ~ v1_relat_1('#skF_5')
    | k1_relat_1(k7_relat_1('#skF_5','#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_504,c_1130])).

tff(c_1159,plain,(
    k1_relat_1(k7_relat_1('#skF_5','#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1149])).

tff(c_24,plain,(
    ! [A_21,B_22] :
      ( v1_relat_1(k7_relat_1(A_21,B_22))
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_77,plain,(
    ! [A_35] :
      ( k1_relat_1(A_35) != k1_xboole_0
      | k1_xboole_0 = A_35
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_84,plain,(
    ! [A_21,B_22] :
      ( k1_relat_1(k7_relat_1(A_21,B_22)) != k1_xboole_0
      | k7_relat_1(A_21,B_22) = k1_xboole_0
      | ~ v1_relat_1(A_21) ) ),
    inference(resolution,[status(thm)],[c_24,c_77])).

tff(c_1181,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1159,c_84])).

tff(c_1200,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1181])).

tff(c_1202,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1200])).

tff(c_1203,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_18,plain,(
    ! [A_16] : r1_xboole_0(A_16,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_16,plain,(
    ! [A_15] : k3_xboole_0(A_15,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1269,plain,(
    ! [A_111,B_112,C_113] :
      ( ~ r1_xboole_0(A_111,B_112)
      | ~ r2_hidden(C_113,k3_xboole_0(A_111,B_112)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1280,plain,(
    ! [A_15,C_113] :
      ( ~ r1_xboole_0(A_15,k1_xboole_0)
      | ~ r2_hidden(C_113,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1269])).

tff(c_1284,plain,(
    ! [C_113] : ~ r2_hidden(C_113,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1280])).

tff(c_28,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1204,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_1679,plain,(
    ! [A_151,C_152,B_153] :
      ( r2_hidden(A_151,k1_relat_1(k7_relat_1(C_152,B_153)))
      | ~ r2_hidden(A_151,k1_relat_1(C_152))
      | ~ r2_hidden(A_151,B_153)
      | ~ v1_relat_1(C_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1694,plain,(
    ! [A_151] :
      ( r2_hidden(A_151,k1_relat_1(k1_xboole_0))
      | ~ r2_hidden(A_151,k1_relat_1('#skF_5'))
      | ~ r2_hidden(A_151,'#skF_4')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1204,c_1679])).

tff(c_1702,plain,(
    ! [A_151] :
      ( r2_hidden(A_151,k1_xboole_0)
      | ~ r2_hidden(A_151,k1_relat_1('#skF_5'))
      | ~ r2_hidden(A_151,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_28,c_1694])).

tff(c_1751,plain,(
    ! [A_154] :
      ( ~ r2_hidden(A_154,k1_relat_1('#skF_5'))
      | ~ r2_hidden(A_154,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1284,c_1702])).

tff(c_1774,plain,(
    ! [B_155] :
      ( ~ r2_hidden('#skF_1'(k1_relat_1('#skF_5'),B_155),'#skF_4')
      | r1_xboole_0(k1_relat_1('#skF_5'),B_155) ) ),
    inference(resolution,[status(thm)],[c_8,c_1751])).

tff(c_1778,plain,(
    r1_xboole_0(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_1774])).

tff(c_1782,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1203,c_1203,c_1778])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:50:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.01/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.52  
% 3.23/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.53  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 3.23/1.53  
% 3.23/1.53  %Foreground sorts:
% 3.23/1.53  
% 3.23/1.53  
% 3.23/1.53  %Background operators:
% 3.23/1.53  
% 3.23/1.53  
% 3.23/1.53  %Foreground operators:
% 3.23/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.23/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.23/1.53  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.23/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.23/1.53  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.23/1.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.23/1.53  tff('#skF_5', type, '#skF_5': $i).
% 3.23/1.53  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.23/1.53  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.23/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.23/1.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.23/1.53  tff('#skF_4', type, '#skF_4': $i).
% 3.23/1.53  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.23/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.23/1.53  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.23/1.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.23/1.53  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.23/1.53  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.23/1.53  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.23/1.53  
% 3.23/1.54  tff(f_107, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 3.23/1.54  tff(f_69, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.23/1.54  tff(f_100, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_relat_1)).
% 3.23/1.54  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.23/1.54  tff(f_81, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 3.23/1.54  tff(f_92, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 3.23/1.54  tff(f_73, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.23/1.54  tff(f_71, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.23/1.54  tff(f_61, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.23/1.54  tff(f_84, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.23/1.54  tff(c_42, plain, (~r1_xboole_0(k1_relat_1('#skF_5'), '#skF_4') | k7_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.23/1.54  tff(c_76, plain, (k7_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_42])).
% 3.23/1.54  tff(c_40, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.23/1.54  tff(c_14, plain, (![A_13]: (r2_hidden('#skF_3'(A_13), A_13) | k1_xboole_0=A_13)), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.23/1.54  tff(c_489, plain, (![A_72, B_73, C_74]: (r2_hidden(A_72, B_73) | ~r2_hidden(A_72, k1_relat_1(k7_relat_1(C_74, B_73))) | ~v1_relat_1(C_74))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.23/1.54  tff(c_504, plain, (![C_74, B_73]: (r2_hidden('#skF_3'(k1_relat_1(k7_relat_1(C_74, B_73))), B_73) | ~v1_relat_1(C_74) | k1_relat_1(k7_relat_1(C_74, B_73))=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_489])).
% 3.23/1.54  tff(c_507, plain, (![A_79, C_80, B_81]: (r2_hidden(A_79, k1_relat_1(C_80)) | ~r2_hidden(A_79, k1_relat_1(k7_relat_1(C_80, B_81))) | ~v1_relat_1(C_80))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.23/1.54  tff(c_898, plain, (![C_97, B_98]: (r2_hidden('#skF_3'(k1_relat_1(k7_relat_1(C_97, B_98))), k1_relat_1(C_97)) | ~v1_relat_1(C_97) | k1_relat_1(k7_relat_1(C_97, B_98))=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_507])).
% 3.23/1.54  tff(c_48, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.23/1.54  tff(c_115, plain, (r1_xboole_0(k1_relat_1('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_76, c_48])).
% 3.23/1.54  tff(c_221, plain, (![A_52, B_53, C_54]: (~r1_xboole_0(A_52, B_53) | ~r2_hidden(C_54, B_53) | ~r2_hidden(C_54, A_52))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.23/1.54  tff(c_231, plain, (![C_54]: (~r2_hidden(C_54, '#skF_4') | ~r2_hidden(C_54, k1_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_115, c_221])).
% 3.23/1.54  tff(c_910, plain, (![B_98]: (~r2_hidden('#skF_3'(k1_relat_1(k7_relat_1('#skF_5', B_98))), '#skF_4') | ~v1_relat_1('#skF_5') | k1_relat_1(k7_relat_1('#skF_5', B_98))=k1_xboole_0)), inference(resolution, [status(thm)], [c_898, c_231])).
% 3.23/1.54  tff(c_1130, plain, (![B_102]: (~r2_hidden('#skF_3'(k1_relat_1(k7_relat_1('#skF_5', B_102))), '#skF_4') | k1_relat_1(k7_relat_1('#skF_5', B_102))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_910])).
% 3.23/1.54  tff(c_1149, plain, (~v1_relat_1('#skF_5') | k1_relat_1(k7_relat_1('#skF_5', '#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_504, c_1130])).
% 3.23/1.54  tff(c_1159, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1149])).
% 3.23/1.54  tff(c_24, plain, (![A_21, B_22]: (v1_relat_1(k7_relat_1(A_21, B_22)) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.23/1.54  tff(c_77, plain, (![A_35]: (k1_relat_1(A_35)!=k1_xboole_0 | k1_xboole_0=A_35 | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.23/1.54  tff(c_84, plain, (![A_21, B_22]: (k1_relat_1(k7_relat_1(A_21, B_22))!=k1_xboole_0 | k7_relat_1(A_21, B_22)=k1_xboole_0 | ~v1_relat_1(A_21))), inference(resolution, [status(thm)], [c_24, c_77])).
% 3.23/1.54  tff(c_1181, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1159, c_84])).
% 3.23/1.54  tff(c_1200, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1181])).
% 3.23/1.54  tff(c_1202, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_1200])).
% 3.23/1.54  tff(c_1203, plain, (~r1_xboole_0(k1_relat_1('#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_42])).
% 3.23/1.54  tff(c_6, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.23/1.54  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.23/1.54  tff(c_18, plain, (![A_16]: (r1_xboole_0(A_16, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.23/1.54  tff(c_16, plain, (![A_15]: (k3_xboole_0(A_15, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.23/1.54  tff(c_1269, plain, (![A_111, B_112, C_113]: (~r1_xboole_0(A_111, B_112) | ~r2_hidden(C_113, k3_xboole_0(A_111, B_112)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.23/1.54  tff(c_1280, plain, (![A_15, C_113]: (~r1_xboole_0(A_15, k1_xboole_0) | ~r2_hidden(C_113, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1269])).
% 3.23/1.54  tff(c_1284, plain, (![C_113]: (~r2_hidden(C_113, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1280])).
% 3.23/1.54  tff(c_28, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.23/1.54  tff(c_1204, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_42])).
% 3.23/1.54  tff(c_1679, plain, (![A_151, C_152, B_153]: (r2_hidden(A_151, k1_relat_1(k7_relat_1(C_152, B_153))) | ~r2_hidden(A_151, k1_relat_1(C_152)) | ~r2_hidden(A_151, B_153) | ~v1_relat_1(C_152))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.23/1.54  tff(c_1694, plain, (![A_151]: (r2_hidden(A_151, k1_relat_1(k1_xboole_0)) | ~r2_hidden(A_151, k1_relat_1('#skF_5')) | ~r2_hidden(A_151, '#skF_4') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1204, c_1679])).
% 3.23/1.54  tff(c_1702, plain, (![A_151]: (r2_hidden(A_151, k1_xboole_0) | ~r2_hidden(A_151, k1_relat_1('#skF_5')) | ~r2_hidden(A_151, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_28, c_1694])).
% 3.23/1.54  tff(c_1751, plain, (![A_154]: (~r2_hidden(A_154, k1_relat_1('#skF_5')) | ~r2_hidden(A_154, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_1284, c_1702])).
% 3.23/1.54  tff(c_1774, plain, (![B_155]: (~r2_hidden('#skF_1'(k1_relat_1('#skF_5'), B_155), '#skF_4') | r1_xboole_0(k1_relat_1('#skF_5'), B_155))), inference(resolution, [status(thm)], [c_8, c_1751])).
% 3.23/1.54  tff(c_1778, plain, (r1_xboole_0(k1_relat_1('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_6, c_1774])).
% 3.23/1.54  tff(c_1782, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1203, c_1203, c_1778])).
% 3.23/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.54  
% 3.23/1.54  Inference rules
% 3.23/1.54  ----------------------
% 3.23/1.54  #Ref     : 0
% 3.23/1.54  #Sup     : 370
% 3.23/1.54  #Fact    : 0
% 3.23/1.54  #Define  : 0
% 3.23/1.54  #Split   : 5
% 3.23/1.54  #Chain   : 0
% 3.23/1.54  #Close   : 0
% 3.23/1.54  
% 3.23/1.54  Ordering : KBO
% 3.23/1.54  
% 3.23/1.54  Simplification rules
% 3.23/1.54  ----------------------
% 3.23/1.54  #Subsume      : 87
% 3.23/1.54  #Demod        : 320
% 3.23/1.54  #Tautology    : 206
% 3.23/1.54  #SimpNegUnit  : 55
% 3.23/1.54  #BackRed      : 1
% 3.23/1.54  
% 3.23/1.54  #Partial instantiations: 0
% 3.23/1.54  #Strategies tried      : 1
% 3.23/1.54  
% 3.23/1.54  Timing (in seconds)
% 3.23/1.54  ----------------------
% 3.23/1.54  Preprocessing        : 0.29
% 3.23/1.54  Parsing              : 0.15
% 3.23/1.54  CNF conversion       : 0.02
% 3.23/1.54  Main loop            : 0.44
% 3.23/1.54  Inferencing          : 0.17
% 3.23/1.54  Reduction            : 0.14
% 3.23/1.54  Demodulation         : 0.10
% 3.23/1.54  BG Simplification    : 0.02
% 3.23/1.54  Subsumption          : 0.08
% 3.23/1.54  Abstraction          : 0.02
% 3.23/1.54  MUC search           : 0.00
% 3.23/1.54  Cooper               : 0.00
% 3.23/1.54  Total                : 0.76
% 3.23/1.55  Index Insertion      : 0.00
% 3.23/1.55  Index Deletion       : 0.00
% 3.23/1.55  Index Matching       : 0.00
% 3.23/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
