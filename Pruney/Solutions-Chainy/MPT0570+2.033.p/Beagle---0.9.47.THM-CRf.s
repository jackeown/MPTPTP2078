%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:45 EST 2020

% Result     : Theorem 9.84s
% Output     : CNFRefutation 9.84s
% Verified   : 
% Statistics : Number of formulae       :   55 (  62 expanded)
%              Number of leaves         :   29 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :   73 (  95 expanded)
%              Number of equality atoms :   21 (  29 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k3_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_5 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_96,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k2_relat_1(B))
            & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).

tff(f_75,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_79,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_77,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_44,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_38,plain,(
    k10_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_40,plain,(
    r1_tarski('#skF_6',k2_relat_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_63,plain,(
    ! [A_36,B_37] : k3_xboole_0(A_36,k2_xboole_0(A_36,B_37)) = A_36 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_24,plain,(
    ! [A_19,B_20] : r1_tarski(k3_xboole_0(A_19,B_20),A_19) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_69,plain,(
    ! [A_36] : r1_tarski(A_36,A_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_24])).

tff(c_255,plain,(
    ! [B_70,A_71] :
      ( r1_xboole_0(k2_relat_1(B_70),A_71)
      | k10_relat_1(B_70,A_71) != k1_xboole_0
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_20,plain,(
    ! [A_14] :
      ( r2_hidden('#skF_5'(A_14),A_14)
      | k1_xboole_0 = A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_76,plain,(
    ! [A_39,B_40,C_41] :
      ( ~ r1_xboole_0(A_39,B_40)
      | ~ r2_hidden(C_41,k3_xboole_0(A_39,B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_87,plain,(
    ! [A_39,B_40] :
      ( ~ r1_xboole_0(A_39,B_40)
      | k3_xboole_0(A_39,B_40) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_76])).

tff(c_1317,plain,(
    ! [B_163,A_164] :
      ( k3_xboole_0(k2_relat_1(B_163),A_164) = k1_xboole_0
      | k10_relat_1(B_163,A_164) != k1_xboole_0
      | ~ v1_relat_1(B_163) ) ),
    inference(resolution,[status(thm)],[c_255,c_87])).

tff(c_26,plain,(
    ! [A_21,B_22,C_23] :
      ( r1_tarski(A_21,k3_xboole_0(B_22,C_23))
      | ~ r1_tarski(A_21,C_23)
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_17295,plain,(
    ! [A_898,A_899,B_900] :
      ( r1_tarski(A_898,k1_xboole_0)
      | ~ r1_tarski(A_898,A_899)
      | ~ r1_tarski(A_898,k2_relat_1(B_900))
      | k10_relat_1(B_900,A_899) != k1_xboole_0
      | ~ v1_relat_1(B_900) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1317,c_26])).

tff(c_17337,plain,(
    ! [A_901,B_902] :
      ( r1_tarski(A_901,k1_xboole_0)
      | ~ r1_tarski(A_901,k2_relat_1(B_902))
      | k10_relat_1(B_902,A_901) != k1_xboole_0
      | ~ v1_relat_1(B_902) ) ),
    inference(resolution,[status(thm)],[c_69,c_17295])).

tff(c_17383,plain,
    ( r1_tarski('#skF_6',k1_xboole_0)
    | k10_relat_1('#skF_7','#skF_6') != k1_xboole_0
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_40,c_17337])).

tff(c_17400,plain,(
    r1_tarski('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_38,c_17383])).

tff(c_140,plain,(
    ! [C_58,B_59,A_60] :
      ( r2_hidden(C_58,B_59)
      | ~ r2_hidden(C_58,A_60)
      | ~ r1_tarski(A_60,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_148,plain,(
    ! [A_64,B_65] :
      ( r2_hidden('#skF_5'(A_64),B_65)
      | ~ r1_tarski(A_64,B_65)
      | k1_xboole_0 = A_64 ) ),
    inference(resolution,[status(thm)],[c_20,c_140])).

tff(c_32,plain,(
    ! [A_27] : r1_xboole_0(A_27,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_30,plain,(
    ! [A_26] : k3_xboole_0(A_26,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_86,plain,(
    ! [A_26,C_41] :
      ( ~ r1_xboole_0(A_26,k1_xboole_0)
      | ~ r2_hidden(C_41,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_76])).

tff(c_89,plain,(
    ! [C_41] : ~ r2_hidden(C_41,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_86])).

tff(c_160,plain,(
    ! [A_64] :
      ( ~ r1_tarski(A_64,k1_xboole_0)
      | k1_xboole_0 = A_64 ) ),
    inference(resolution,[status(thm)],[c_148,c_89])).

tff(c_17493,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_17400,c_160])).

tff(c_17577,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_17493])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:40:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.84/3.81  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.84/3.81  
% 9.84/3.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.84/3.81  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k3_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_5 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_1 > #skF_4
% 9.84/3.81  
% 9.84/3.81  %Foreground sorts:
% 9.84/3.81  
% 9.84/3.81  
% 9.84/3.81  %Background operators:
% 9.84/3.81  
% 9.84/3.81  
% 9.84/3.81  %Foreground operators:
% 9.84/3.81  tff('#skF_5', type, '#skF_5': $i > $i).
% 9.84/3.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.84/3.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.84/3.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.84/3.81  tff('#skF_7', type, '#skF_7': $i).
% 9.84/3.81  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 9.84/3.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.84/3.81  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.84/3.81  tff('#skF_6', type, '#skF_6': $i).
% 9.84/3.81  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.84/3.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.84/3.81  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 9.84/3.81  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.84/3.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.84/3.81  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.84/3.81  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.84/3.81  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.84/3.81  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.84/3.81  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 9.84/3.81  
% 9.84/3.82  tff(f_96, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_relat_1)).
% 9.84/3.82  tff(f_75, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 9.84/3.82  tff(f_67, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 9.84/3.82  tff(f_85, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 9.84/3.82  tff(f_61, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 9.84/3.82  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 9.84/3.82  tff(f_73, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 9.84/3.82  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 9.84/3.82  tff(f_79, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 9.84/3.82  tff(f_77, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 9.84/3.82  tff(c_42, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.84/3.82  tff(c_44, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.84/3.82  tff(c_38, plain, (k10_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.84/3.82  tff(c_40, plain, (r1_tarski('#skF_6', k2_relat_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.84/3.82  tff(c_63, plain, (![A_36, B_37]: (k3_xboole_0(A_36, k2_xboole_0(A_36, B_37))=A_36)), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.84/3.82  tff(c_24, plain, (![A_19, B_20]: (r1_tarski(k3_xboole_0(A_19, B_20), A_19))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.84/3.82  tff(c_69, plain, (![A_36]: (r1_tarski(A_36, A_36))), inference(superposition, [status(thm), theory('equality')], [c_63, c_24])).
% 9.84/3.82  tff(c_255, plain, (![B_70, A_71]: (r1_xboole_0(k2_relat_1(B_70), A_71) | k10_relat_1(B_70, A_71)!=k1_xboole_0 | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_85])).
% 9.84/3.82  tff(c_20, plain, (![A_14]: (r2_hidden('#skF_5'(A_14), A_14) | k1_xboole_0=A_14)), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.84/3.82  tff(c_76, plain, (![A_39, B_40, C_41]: (~r1_xboole_0(A_39, B_40) | ~r2_hidden(C_41, k3_xboole_0(A_39, B_40)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.84/3.82  tff(c_87, plain, (![A_39, B_40]: (~r1_xboole_0(A_39, B_40) | k3_xboole_0(A_39, B_40)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_76])).
% 9.84/3.82  tff(c_1317, plain, (![B_163, A_164]: (k3_xboole_0(k2_relat_1(B_163), A_164)=k1_xboole_0 | k10_relat_1(B_163, A_164)!=k1_xboole_0 | ~v1_relat_1(B_163))), inference(resolution, [status(thm)], [c_255, c_87])).
% 9.84/3.82  tff(c_26, plain, (![A_21, B_22, C_23]: (r1_tarski(A_21, k3_xboole_0(B_22, C_23)) | ~r1_tarski(A_21, C_23) | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.84/3.82  tff(c_17295, plain, (![A_898, A_899, B_900]: (r1_tarski(A_898, k1_xboole_0) | ~r1_tarski(A_898, A_899) | ~r1_tarski(A_898, k2_relat_1(B_900)) | k10_relat_1(B_900, A_899)!=k1_xboole_0 | ~v1_relat_1(B_900))), inference(superposition, [status(thm), theory('equality')], [c_1317, c_26])).
% 9.84/3.82  tff(c_17337, plain, (![A_901, B_902]: (r1_tarski(A_901, k1_xboole_0) | ~r1_tarski(A_901, k2_relat_1(B_902)) | k10_relat_1(B_902, A_901)!=k1_xboole_0 | ~v1_relat_1(B_902))), inference(resolution, [status(thm)], [c_69, c_17295])).
% 9.84/3.82  tff(c_17383, plain, (r1_tarski('#skF_6', k1_xboole_0) | k10_relat_1('#skF_7', '#skF_6')!=k1_xboole_0 | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_40, c_17337])).
% 9.84/3.82  tff(c_17400, plain, (r1_tarski('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_38, c_17383])).
% 9.84/3.82  tff(c_140, plain, (![C_58, B_59, A_60]: (r2_hidden(C_58, B_59) | ~r2_hidden(C_58, A_60) | ~r1_tarski(A_60, B_59))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.84/3.82  tff(c_148, plain, (![A_64, B_65]: (r2_hidden('#skF_5'(A_64), B_65) | ~r1_tarski(A_64, B_65) | k1_xboole_0=A_64)), inference(resolution, [status(thm)], [c_20, c_140])).
% 9.84/3.82  tff(c_32, plain, (![A_27]: (r1_xboole_0(A_27, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.84/3.82  tff(c_30, plain, (![A_26]: (k3_xboole_0(A_26, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.84/3.82  tff(c_86, plain, (![A_26, C_41]: (~r1_xboole_0(A_26, k1_xboole_0) | ~r2_hidden(C_41, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_30, c_76])).
% 9.84/3.82  tff(c_89, plain, (![C_41]: (~r2_hidden(C_41, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_86])).
% 9.84/3.82  tff(c_160, plain, (![A_64]: (~r1_tarski(A_64, k1_xboole_0) | k1_xboole_0=A_64)), inference(resolution, [status(thm)], [c_148, c_89])).
% 9.84/3.82  tff(c_17493, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_17400, c_160])).
% 9.84/3.82  tff(c_17577, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_17493])).
% 9.84/3.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.84/3.82  
% 9.84/3.82  Inference rules
% 9.84/3.82  ----------------------
% 9.84/3.82  #Ref     : 0
% 9.84/3.82  #Sup     : 4698
% 9.84/3.82  #Fact    : 0
% 9.84/3.82  #Define  : 0
% 9.84/3.82  #Split   : 4
% 9.84/3.82  #Chain   : 0
% 9.84/3.82  #Close   : 0
% 9.84/3.82  
% 9.84/3.82  Ordering : KBO
% 9.84/3.82  
% 9.84/3.82  Simplification rules
% 9.84/3.82  ----------------------
% 9.84/3.82  #Subsume      : 2767
% 9.84/3.82  #Demod        : 1310
% 9.84/3.82  #Tautology    : 561
% 9.84/3.82  #SimpNegUnit  : 40
% 9.84/3.82  #BackRed      : 0
% 9.84/3.82  
% 9.84/3.82  #Partial instantiations: 0
% 9.84/3.82  #Strategies tried      : 1
% 9.84/3.82  
% 9.84/3.82  Timing (in seconds)
% 9.84/3.82  ----------------------
% 9.84/3.83  Preprocessing        : 0.31
% 9.84/3.83  Parsing              : 0.17
% 9.84/3.83  CNF conversion       : 0.02
% 9.84/3.83  Main loop            : 2.75
% 9.84/3.83  Inferencing          : 0.67
% 9.84/3.83  Reduction            : 0.64
% 9.84/3.83  Demodulation         : 0.44
% 9.84/3.83  BG Simplification    : 0.06
% 9.84/3.83  Subsumption          : 1.24
% 9.84/3.83  Abstraction          : 0.09
% 9.84/3.83  MUC search           : 0.00
% 9.84/3.83  Cooper               : 0.00
% 9.84/3.83  Total                : 3.08
% 9.84/3.83  Index Insertion      : 0.00
% 9.84/3.83  Index Deletion       : 0.00
% 9.84/3.83  Index Matching       : 0.00
% 9.84/3.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
