%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:45 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :   61 (  85 expanded)
%              Number of leaves         :   24 (  38 expanded)
%              Depth                    :   11
%              Number of atoms          :  100 ( 164 expanded)
%              Number of equality atoms :   25 (  41 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k7_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_57,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_69,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_34,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3')
    | k7_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_67,plain,(
    k7_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_32,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_10,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_148,plain,(
    ! [A_39,B_40,C_41] :
      ( r2_hidden(A_39,B_40)
      | ~ r2_hidden(A_39,k1_relat_1(k7_relat_1(C_41,B_40)))
      | ~ v1_relat_1(C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_163,plain,(
    ! [C_41,B_40] :
      ( r2_hidden('#skF_2'(k1_relat_1(k7_relat_1(C_41,B_40))),B_40)
      | ~ v1_relat_1(C_41)
      | k1_relat_1(k7_relat_1(C_41,B_40)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_148])).

tff(c_178,plain,(
    ! [A_44,C_45,B_46] :
      ( r2_hidden(A_44,k1_relat_1(C_45))
      | ~ r2_hidden(A_44,k1_relat_1(k7_relat_1(C_45,B_46)))
      | ~ v1_relat_1(C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_441,plain,(
    ! [C_61,B_62] :
      ( r2_hidden('#skF_2'(k1_relat_1(k7_relat_1(C_61,B_62))),k1_relat_1(C_61))
      | ~ v1_relat_1(C_61)
      | k1_relat_1(k7_relat_1(C_61,B_62)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_178])).

tff(c_40,plain,
    ( k7_relat_1('#skF_4','#skF_3') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_102,plain,(
    r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_40])).

tff(c_117,plain,(
    ! [A_35,B_36,C_37] :
      ( ~ r1_xboole_0(A_35,B_36)
      | ~ r2_hidden(C_37,B_36)
      | ~ r2_hidden(C_37,A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_127,plain,(
    ! [C_37] :
      ( ~ r2_hidden(C_37,'#skF_3')
      | ~ r2_hidden(C_37,k1_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_102,c_117])).

tff(c_453,plain,(
    ! [B_62] :
      ( ~ r2_hidden('#skF_2'(k1_relat_1(k7_relat_1('#skF_4',B_62))),'#skF_3')
      | ~ v1_relat_1('#skF_4')
      | k1_relat_1(k7_relat_1('#skF_4',B_62)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_441,c_127])).

tff(c_904,plain,(
    ! [B_83] :
      ( ~ r2_hidden('#skF_2'(k1_relat_1(k7_relat_1('#skF_4',B_83))),'#skF_3')
      | k1_relat_1(k7_relat_1('#skF_4',B_83)) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_453])).

tff(c_915,plain,
    ( ~ v1_relat_1('#skF_4')
    | k1_relat_1(k7_relat_1('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_163,c_904])).

tff(c_921,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_915])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( v1_relat_1(k7_relat_1(A_13,B_14))
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_75,plain,(
    ! [A_29] :
      ( k1_relat_1(A_29) != k1_xboole_0
      | k1_xboole_0 = A_29
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_82,plain,(
    ! [A_13,B_14] :
      ( k1_relat_1(k7_relat_1(A_13,B_14)) != k1_xboole_0
      | k7_relat_1(A_13,B_14) = k1_xboole_0
      | ~ v1_relat_1(A_13) ) ),
    inference(resolution,[status(thm)],[c_16,c_75])).

tff(c_969,plain,
    ( k7_relat_1('#skF_4','#skF_3') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_921,c_82])).

tff(c_997,plain,(
    k7_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_969])).

tff(c_999,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_997])).

tff(c_1000,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_34])).

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

tff(c_12,plain,(
    ! [A_10] : r1_xboole_0(A_10,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_61,plain,(
    ! [A_26,B_27] :
      ( ~ r2_hidden(A_26,B_27)
      | ~ r1_xboole_0(k1_tarski(A_26),B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_66,plain,(
    ! [A_26] : ~ r2_hidden(A_26,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_61])).

tff(c_20,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1001,plain,(
    k7_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_1129,plain,(
    ! [A_106,C_107,B_108] :
      ( r2_hidden(A_106,k1_relat_1(k7_relat_1(C_107,B_108)))
      | ~ r2_hidden(A_106,k1_relat_1(C_107))
      | ~ r2_hidden(A_106,B_108)
      | ~ v1_relat_1(C_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1138,plain,(
    ! [A_106] :
      ( r2_hidden(A_106,k1_relat_1(k1_xboole_0))
      | ~ r2_hidden(A_106,k1_relat_1('#skF_4'))
      | ~ r2_hidden(A_106,'#skF_3')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1001,c_1129])).

tff(c_1142,plain,(
    ! [A_106] :
      ( r2_hidden(A_106,k1_xboole_0)
      | ~ r2_hidden(A_106,k1_relat_1('#skF_4'))
      | ~ r2_hidden(A_106,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_20,c_1138])).

tff(c_1144,plain,(
    ! [A_109] :
      ( ~ r2_hidden(A_109,k1_relat_1('#skF_4'))
      | ~ r2_hidden(A_109,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1142])).

tff(c_1162,plain,(
    ! [B_110] :
      ( ~ r2_hidden('#skF_1'(k1_relat_1('#skF_4'),B_110),'#skF_3')
      | r1_xboole_0(k1_relat_1('#skF_4'),B_110) ) ),
    inference(resolution,[status(thm)],[c_8,c_1144])).

tff(c_1166,plain,(
    r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_1162])).

tff(c_1170,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1000,c_1000,c_1166])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:04:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.70/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.42  
% 2.70/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.42  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.70/1.42  
% 2.70/1.42  %Foreground sorts:
% 2.70/1.42  
% 2.70/1.42  
% 2.70/1.42  %Background operators:
% 2.70/1.42  
% 2.70/1.42  
% 2.70/1.42  %Foreground operators:
% 2.70/1.42  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.70/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.70/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.70/1.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.70/1.42  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.70/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.70/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.70/1.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.70/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.70/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.70/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.70/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.70/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.70/1.42  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.70/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.70/1.42  
% 2.92/1.44  tff(f_92, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 2.92/1.44  tff(f_55, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.92/1.44  tff(f_85, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 2.92/1.44  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.92/1.44  tff(f_66, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.92/1.44  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 2.92/1.44  tff(f_57, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.92/1.44  tff(f_62, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.92/1.44  tff(f_69, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.92/1.44  tff(c_34, plain, (~r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3') | k7_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.92/1.44  tff(c_67, plain, (k7_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_34])).
% 2.92/1.44  tff(c_32, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.92/1.44  tff(c_10, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.92/1.44  tff(c_148, plain, (![A_39, B_40, C_41]: (r2_hidden(A_39, B_40) | ~r2_hidden(A_39, k1_relat_1(k7_relat_1(C_41, B_40))) | ~v1_relat_1(C_41))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.92/1.44  tff(c_163, plain, (![C_41, B_40]: (r2_hidden('#skF_2'(k1_relat_1(k7_relat_1(C_41, B_40))), B_40) | ~v1_relat_1(C_41) | k1_relat_1(k7_relat_1(C_41, B_40))=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_148])).
% 2.92/1.44  tff(c_178, plain, (![A_44, C_45, B_46]: (r2_hidden(A_44, k1_relat_1(C_45)) | ~r2_hidden(A_44, k1_relat_1(k7_relat_1(C_45, B_46))) | ~v1_relat_1(C_45))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.92/1.44  tff(c_441, plain, (![C_61, B_62]: (r2_hidden('#skF_2'(k1_relat_1(k7_relat_1(C_61, B_62))), k1_relat_1(C_61)) | ~v1_relat_1(C_61) | k1_relat_1(k7_relat_1(C_61, B_62))=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_178])).
% 2.92/1.44  tff(c_40, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.92/1.44  tff(c_102, plain, (r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_67, c_40])).
% 2.92/1.44  tff(c_117, plain, (![A_35, B_36, C_37]: (~r1_xboole_0(A_35, B_36) | ~r2_hidden(C_37, B_36) | ~r2_hidden(C_37, A_35))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.92/1.44  tff(c_127, plain, (![C_37]: (~r2_hidden(C_37, '#skF_3') | ~r2_hidden(C_37, k1_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_102, c_117])).
% 2.92/1.44  tff(c_453, plain, (![B_62]: (~r2_hidden('#skF_2'(k1_relat_1(k7_relat_1('#skF_4', B_62))), '#skF_3') | ~v1_relat_1('#skF_4') | k1_relat_1(k7_relat_1('#skF_4', B_62))=k1_xboole_0)), inference(resolution, [status(thm)], [c_441, c_127])).
% 2.92/1.44  tff(c_904, plain, (![B_83]: (~r2_hidden('#skF_2'(k1_relat_1(k7_relat_1('#skF_4', B_83))), '#skF_3') | k1_relat_1(k7_relat_1('#skF_4', B_83))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_453])).
% 2.92/1.44  tff(c_915, plain, (~v1_relat_1('#skF_4') | k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_163, c_904])).
% 2.92/1.44  tff(c_921, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_915])).
% 2.92/1.44  tff(c_16, plain, (![A_13, B_14]: (v1_relat_1(k7_relat_1(A_13, B_14)) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.92/1.44  tff(c_75, plain, (![A_29]: (k1_relat_1(A_29)!=k1_xboole_0 | k1_xboole_0=A_29 | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.92/1.44  tff(c_82, plain, (![A_13, B_14]: (k1_relat_1(k7_relat_1(A_13, B_14))!=k1_xboole_0 | k7_relat_1(A_13, B_14)=k1_xboole_0 | ~v1_relat_1(A_13))), inference(resolution, [status(thm)], [c_16, c_75])).
% 2.92/1.44  tff(c_969, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_921, c_82])).
% 2.92/1.44  tff(c_997, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_969])).
% 2.92/1.44  tff(c_999, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_997])).
% 2.92/1.44  tff(c_1000, plain, (~r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_34])).
% 2.92/1.44  tff(c_6, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.92/1.44  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.92/1.44  tff(c_12, plain, (![A_10]: (r1_xboole_0(A_10, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.92/1.44  tff(c_61, plain, (![A_26, B_27]: (~r2_hidden(A_26, B_27) | ~r1_xboole_0(k1_tarski(A_26), B_27))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.92/1.44  tff(c_66, plain, (![A_26]: (~r2_hidden(A_26, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_61])).
% 2.92/1.44  tff(c_20, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.92/1.44  tff(c_1001, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_34])).
% 2.92/1.44  tff(c_1129, plain, (![A_106, C_107, B_108]: (r2_hidden(A_106, k1_relat_1(k7_relat_1(C_107, B_108))) | ~r2_hidden(A_106, k1_relat_1(C_107)) | ~r2_hidden(A_106, B_108) | ~v1_relat_1(C_107))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.92/1.44  tff(c_1138, plain, (![A_106]: (r2_hidden(A_106, k1_relat_1(k1_xboole_0)) | ~r2_hidden(A_106, k1_relat_1('#skF_4')) | ~r2_hidden(A_106, '#skF_3') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1001, c_1129])).
% 2.92/1.44  tff(c_1142, plain, (![A_106]: (r2_hidden(A_106, k1_xboole_0) | ~r2_hidden(A_106, k1_relat_1('#skF_4')) | ~r2_hidden(A_106, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_20, c_1138])).
% 2.92/1.44  tff(c_1144, plain, (![A_109]: (~r2_hidden(A_109, k1_relat_1('#skF_4')) | ~r2_hidden(A_109, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_66, c_1142])).
% 2.92/1.44  tff(c_1162, plain, (![B_110]: (~r2_hidden('#skF_1'(k1_relat_1('#skF_4'), B_110), '#skF_3') | r1_xboole_0(k1_relat_1('#skF_4'), B_110))), inference(resolution, [status(thm)], [c_8, c_1144])).
% 2.92/1.44  tff(c_1166, plain, (r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_6, c_1162])).
% 2.92/1.44  tff(c_1170, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1000, c_1000, c_1166])).
% 2.92/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.92/1.44  
% 2.92/1.44  Inference rules
% 2.92/1.44  ----------------------
% 2.92/1.44  #Ref     : 0
% 2.92/1.44  #Sup     : 227
% 2.92/1.44  #Fact    : 0
% 2.92/1.44  #Define  : 0
% 2.92/1.44  #Split   : 5
% 2.92/1.44  #Chain   : 0
% 2.92/1.44  #Close   : 0
% 2.92/1.44  
% 2.92/1.44  Ordering : KBO
% 2.92/1.44  
% 2.92/1.44  Simplification rules
% 2.92/1.44  ----------------------
% 2.92/1.44  #Subsume      : 51
% 2.92/1.44  #Demod        : 241
% 2.92/1.44  #Tautology    : 103
% 2.92/1.44  #SimpNegUnit  : 38
% 2.92/1.44  #BackRed      : 1
% 2.92/1.44  
% 2.92/1.44  #Partial instantiations: 0
% 2.92/1.44  #Strategies tried      : 1
% 2.92/1.44  
% 2.92/1.44  Timing (in seconds)
% 2.92/1.44  ----------------------
% 2.92/1.44  Preprocessing        : 0.28
% 2.92/1.44  Parsing              : 0.16
% 2.92/1.44  CNF conversion       : 0.02
% 2.92/1.44  Main loop            : 0.39
% 2.92/1.44  Inferencing          : 0.15
% 2.92/1.44  Reduction            : 0.11
% 2.92/1.44  Demodulation         : 0.08
% 2.92/1.44  BG Simplification    : 0.02
% 2.92/1.44  Subsumption          : 0.08
% 2.92/1.44  Abstraction          : 0.02
% 2.92/1.44  MUC search           : 0.00
% 2.92/1.44  Cooper               : 0.00
% 2.92/1.44  Total                : 0.70
% 2.92/1.44  Index Insertion      : 0.00
% 2.92/1.44  Index Deletion       : 0.00
% 2.92/1.44  Index Matching       : 0.00
% 2.92/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
