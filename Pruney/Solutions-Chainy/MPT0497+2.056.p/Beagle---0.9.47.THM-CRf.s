%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:46 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :   65 (  86 expanded)
%              Number of leaves         :   30 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :   93 ( 145 expanded)
%              Number of equality atoms :   27 (  42 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_88,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_69,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_67,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_80,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

tff(c_42,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_5'),'#skF_4')
    | k7_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_85,plain,(
    k7_relat_1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_40,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_412,plain,(
    ! [B_68,A_69] :
      ( k3_xboole_0(k1_relat_1(B_68),A_69) = k1_relat_1(k7_relat_1(B_68,A_69))
      | ~ v1_relat_1(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_48,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_124,plain,(
    r1_xboole_0(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_48])).

tff(c_12,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_3'(A_11),A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_105,plain,(
    ! [A_38,B_39,C_40] :
      ( ~ r1_xboole_0(A_38,B_39)
      | ~ r2_hidden(C_40,k3_xboole_0(A_38,B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_125,plain,(
    ! [A_42,B_43] :
      ( ~ r1_xboole_0(A_42,B_43)
      | k3_xboole_0(A_42,B_43) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_105])).

tff(c_132,plain,(
    k3_xboole_0(k1_relat_1('#skF_5'),'#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_124,c_125])).

tff(c_437,plain,
    ( k1_relat_1(k7_relat_1('#skF_5','#skF_4')) = k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_412,c_132])).

tff(c_464,plain,(
    k1_relat_1(k7_relat_1('#skF_5','#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_437])).

tff(c_22,plain,(
    ! [A_19,B_20] :
      ( v1_relat_1(k7_relat_1(A_19,B_20))
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_96,plain,(
    ! [A_37] :
      ( k1_relat_1(A_37) != k1_xboole_0
      | k1_xboole_0 = A_37
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_595,plain,(
    ! [A_79,B_80] :
      ( k1_relat_1(k7_relat_1(A_79,B_80)) != k1_xboole_0
      | k7_relat_1(A_79,B_80) = k1_xboole_0
      | ~ v1_relat_1(A_79) ) ),
    inference(resolution,[status(thm)],[c_22,c_96])).

tff(c_601,plain,
    ( k7_relat_1('#skF_5','#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_464,c_595])).

tff(c_605,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_601])).

tff(c_607,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_605])).

tff(c_608,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_14] : r1_xboole_0(A_14,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_14,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_655,plain,(
    ! [A_84,B_85,C_86] :
      ( ~ r1_xboole_0(A_84,B_85)
      | ~ r2_hidden(C_86,k3_xboole_0(A_84,B_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_662,plain,(
    ! [A_13,C_86] :
      ( ~ r1_xboole_0(A_13,k1_xboole_0)
      | ~ r2_hidden(C_86,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_655])).

tff(c_665,plain,(
    ! [C_86] : ~ r2_hidden(C_86,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_662])).

tff(c_26,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_610,plain,(
    k7_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_608,c_48])).

tff(c_1255,plain,(
    ! [A_134,C_135,B_136] :
      ( r2_hidden(A_134,k1_relat_1(k7_relat_1(C_135,B_136)))
      | ~ r2_hidden(A_134,k1_relat_1(C_135))
      | ~ r2_hidden(A_134,B_136)
      | ~ v1_relat_1(C_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1279,plain,(
    ! [A_134] :
      ( r2_hidden(A_134,k1_relat_1(k1_xboole_0))
      | ~ r2_hidden(A_134,k1_relat_1('#skF_5'))
      | ~ r2_hidden(A_134,'#skF_4')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_610,c_1255])).

tff(c_1293,plain,(
    ! [A_134] :
      ( r2_hidden(A_134,k1_xboole_0)
      | ~ r2_hidden(A_134,k1_relat_1('#skF_5'))
      | ~ r2_hidden(A_134,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_26,c_1279])).

tff(c_1295,plain,(
    ! [A_137] :
      ( ~ r2_hidden(A_137,k1_relat_1('#skF_5'))
      | ~ r2_hidden(A_137,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_665,c_1293])).

tff(c_1319,plain,(
    ! [B_139] :
      ( ~ r2_hidden('#skF_1'(k1_relat_1('#skF_5'),B_139),'#skF_4')
      | r1_xboole_0(k1_relat_1('#skF_5'),B_139) ) ),
    inference(resolution,[status(thm)],[c_6,c_1295])).

tff(c_1323,plain,(
    r1_xboole_0(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_1319])).

tff(c_1327,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_608,c_608,c_1323])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:37:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.79/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.41  
% 2.79/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.42  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 2.79/1.42  
% 2.79/1.42  %Foreground sorts:
% 2.79/1.42  
% 2.79/1.42  
% 2.79/1.42  %Background operators:
% 2.79/1.42  
% 2.79/1.42  
% 2.79/1.42  %Foreground operators:
% 2.79/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.79/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.79/1.42  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.79/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.79/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.79/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.79/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.79/1.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.79/1.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.79/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.79/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.79/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.79/1.42  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.79/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.79/1.42  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.79/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.79/1.42  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.79/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.79/1.42  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.79/1.42  
% 2.79/1.43  tff(f_107, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 2.79/1.43  tff(f_100, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 2.79/1.43  tff(f_65, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.79/1.43  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.79/1.43  tff(f_77, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.79/1.43  tff(f_88, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 2.79/1.43  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.79/1.43  tff(f_69, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.79/1.43  tff(f_67, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.79/1.43  tff(f_80, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.79/1.43  tff(f_96, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 2.79/1.43  tff(c_42, plain, (~r1_xboole_0(k1_relat_1('#skF_5'), '#skF_4') | k7_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.79/1.43  tff(c_85, plain, (k7_relat_1('#skF_5', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_42])).
% 2.79/1.43  tff(c_40, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.79/1.43  tff(c_412, plain, (![B_68, A_69]: (k3_xboole_0(k1_relat_1(B_68), A_69)=k1_relat_1(k7_relat_1(B_68, A_69)) | ~v1_relat_1(B_68))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.79/1.43  tff(c_48, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.79/1.43  tff(c_124, plain, (r1_xboole_0(k1_relat_1('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_85, c_48])).
% 2.79/1.43  tff(c_12, plain, (![A_11]: (r2_hidden('#skF_3'(A_11), A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.79/1.43  tff(c_105, plain, (![A_38, B_39, C_40]: (~r1_xboole_0(A_38, B_39) | ~r2_hidden(C_40, k3_xboole_0(A_38, B_39)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.79/1.43  tff(c_125, plain, (![A_42, B_43]: (~r1_xboole_0(A_42, B_43) | k3_xboole_0(A_42, B_43)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_105])).
% 2.79/1.43  tff(c_132, plain, (k3_xboole_0(k1_relat_1('#skF_5'), '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_124, c_125])).
% 2.79/1.43  tff(c_437, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_4'))=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_412, c_132])).
% 2.79/1.43  tff(c_464, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_40, c_437])).
% 2.79/1.43  tff(c_22, plain, (![A_19, B_20]: (v1_relat_1(k7_relat_1(A_19, B_20)) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.79/1.43  tff(c_96, plain, (![A_37]: (k1_relat_1(A_37)!=k1_xboole_0 | k1_xboole_0=A_37 | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.79/1.43  tff(c_595, plain, (![A_79, B_80]: (k1_relat_1(k7_relat_1(A_79, B_80))!=k1_xboole_0 | k7_relat_1(A_79, B_80)=k1_xboole_0 | ~v1_relat_1(A_79))), inference(resolution, [status(thm)], [c_22, c_96])).
% 2.79/1.43  tff(c_601, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_464, c_595])).
% 2.79/1.43  tff(c_605, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_40, c_601])).
% 2.79/1.43  tff(c_607, plain, $false, inference(negUnitSimplification, [status(thm)], [c_85, c_605])).
% 2.79/1.43  tff(c_608, plain, (~r1_xboole_0(k1_relat_1('#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_42])).
% 2.79/1.43  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.79/1.43  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.79/1.43  tff(c_16, plain, (![A_14]: (r1_xboole_0(A_14, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.79/1.43  tff(c_14, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.79/1.43  tff(c_655, plain, (![A_84, B_85, C_86]: (~r1_xboole_0(A_84, B_85) | ~r2_hidden(C_86, k3_xboole_0(A_84, B_85)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.79/1.43  tff(c_662, plain, (![A_13, C_86]: (~r1_xboole_0(A_13, k1_xboole_0) | ~r2_hidden(C_86, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_655])).
% 2.79/1.43  tff(c_665, plain, (![C_86]: (~r2_hidden(C_86, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_662])).
% 2.79/1.43  tff(c_26, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.79/1.43  tff(c_610, plain, (k7_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_608, c_48])).
% 2.79/1.43  tff(c_1255, plain, (![A_134, C_135, B_136]: (r2_hidden(A_134, k1_relat_1(k7_relat_1(C_135, B_136))) | ~r2_hidden(A_134, k1_relat_1(C_135)) | ~r2_hidden(A_134, B_136) | ~v1_relat_1(C_135))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.79/1.43  tff(c_1279, plain, (![A_134]: (r2_hidden(A_134, k1_relat_1(k1_xboole_0)) | ~r2_hidden(A_134, k1_relat_1('#skF_5')) | ~r2_hidden(A_134, '#skF_4') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_610, c_1255])).
% 2.79/1.43  tff(c_1293, plain, (![A_134]: (r2_hidden(A_134, k1_xboole_0) | ~r2_hidden(A_134, k1_relat_1('#skF_5')) | ~r2_hidden(A_134, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_26, c_1279])).
% 2.79/1.43  tff(c_1295, plain, (![A_137]: (~r2_hidden(A_137, k1_relat_1('#skF_5')) | ~r2_hidden(A_137, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_665, c_1293])).
% 2.79/1.43  tff(c_1319, plain, (![B_139]: (~r2_hidden('#skF_1'(k1_relat_1('#skF_5'), B_139), '#skF_4') | r1_xboole_0(k1_relat_1('#skF_5'), B_139))), inference(resolution, [status(thm)], [c_6, c_1295])).
% 2.79/1.43  tff(c_1323, plain, (r1_xboole_0(k1_relat_1('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_4, c_1319])).
% 2.79/1.43  tff(c_1327, plain, $false, inference(negUnitSimplification, [status(thm)], [c_608, c_608, c_1323])).
% 2.79/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.43  
% 2.79/1.43  Inference rules
% 2.79/1.43  ----------------------
% 2.79/1.43  #Ref     : 0
% 2.79/1.43  #Sup     : 280
% 2.79/1.43  #Fact    : 0
% 2.79/1.43  #Define  : 0
% 2.79/1.43  #Split   : 6
% 2.79/1.43  #Chain   : 0
% 2.79/1.43  #Close   : 0
% 2.79/1.43  
% 2.79/1.43  Ordering : KBO
% 2.79/1.43  
% 2.79/1.43  Simplification rules
% 2.79/1.43  ----------------------
% 2.79/1.43  #Subsume      : 50
% 2.79/1.43  #Demod        : 187
% 2.79/1.43  #Tautology    : 153
% 2.79/1.43  #SimpNegUnit  : 26
% 2.79/1.43  #BackRed      : 1
% 2.79/1.43  
% 2.79/1.43  #Partial instantiations: 0
% 2.79/1.43  #Strategies tried      : 1
% 2.79/1.43  
% 2.79/1.43  Timing (in seconds)
% 2.79/1.43  ----------------------
% 2.79/1.43  Preprocessing        : 0.30
% 2.79/1.43  Parsing              : 0.16
% 2.79/1.43  CNF conversion       : 0.02
% 2.79/1.43  Main loop            : 0.37
% 2.79/1.43  Inferencing          : 0.14
% 2.79/1.43  Reduction            : 0.11
% 2.79/1.43  Demodulation         : 0.08
% 2.79/1.43  BG Simplification    : 0.02
% 2.79/1.43  Subsumption          : 0.07
% 2.79/1.43  Abstraction          : 0.02
% 2.79/1.43  MUC search           : 0.00
% 2.79/1.43  Cooper               : 0.00
% 2.79/1.43  Total                : 0.70
% 2.79/1.43  Index Insertion      : 0.00
% 2.79/1.43  Index Deletion       : 0.00
% 2.79/1.43  Index Matching       : 0.00
% 2.79/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
