%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:45 EST 2020

% Result     : Theorem 3.30s
% Output     : CNFRefutation 3.30s
% Verified   : 
% Statistics : Number of formulae       :   54 (  64 expanded)
%              Number of leaves         :   24 (  33 expanded)
%              Depth                    :   11
%              Number of atoms          :   91 ( 128 expanded)
%              Number of equality atoms :   19 (  25 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_81,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k2_relat_1(B))
            & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_59,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_57,axiom,(
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

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_30,plain,(
    k10_relat_1('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_64,plain,(
    ! [A_30,B_31] :
      ( r2_hidden('#skF_1'(A_30,B_31),A_30)
      | r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_73,plain,(
    ! [A_30] : r1_tarski(A_30,A_30) ),
    inference(resolution,[status(thm)],[c_64,c_4])).

tff(c_295,plain,(
    ! [A_82,B_83] :
      ( r2_hidden('#skF_2'(A_82,B_83),B_83)
      | r2_hidden('#skF_3'(A_82,B_83),A_82)
      | B_83 = A_82 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    ! [A_14] : r1_xboole_0(A_14,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_42,plain,(
    ! [A_20,B_21] :
      ( ~ r2_hidden(A_20,B_21)
      | ~ r1_xboole_0(k1_tarski(A_20),B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_47,plain,(
    ! [A_20] : ~ r2_hidden(A_20,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_22,c_42])).

tff(c_329,plain,(
    ! [B_83] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_83),B_83)
      | k1_xboole_0 = B_83 ) ),
    inference(resolution,[status(thm)],[c_295,c_47])).

tff(c_36,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_32,plain,(
    r1_tarski('#skF_5',k2_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_18,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_4'(A_9,B_10),B_10)
      | r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_84,plain,(
    ! [C_37,B_38,A_39] :
      ( r2_hidden(C_37,B_38)
      | ~ r2_hidden(C_37,A_39)
      | ~ r1_tarski(A_39,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_202,plain,(
    ! [A_70,B_71,B_72] :
      ( r2_hidden('#skF_4'(A_70,B_71),B_72)
      | ~ r1_tarski(B_71,B_72)
      | r1_xboole_0(A_70,B_71) ) ),
    inference(resolution,[status(thm)],[c_18,c_84])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_959,plain,(
    ! [A_164,B_165,B_166,B_167] :
      ( r2_hidden('#skF_4'(A_164,B_165),B_166)
      | ~ r1_tarski(B_167,B_166)
      | ~ r1_tarski(B_165,B_167)
      | r1_xboole_0(A_164,B_165) ) ),
    inference(resolution,[status(thm)],[c_202,c_2])).

tff(c_968,plain,(
    ! [A_164,B_165] :
      ( r2_hidden('#skF_4'(A_164,B_165),k2_relat_1('#skF_6'))
      | ~ r1_tarski(B_165,'#skF_5')
      | r1_xboole_0(A_164,B_165) ) ),
    inference(resolution,[status(thm)],[c_32,c_959])).

tff(c_109,plain,(
    ! [B_43,A_44] :
      ( r1_xboole_0(k2_relat_1(B_43),A_44)
      | k10_relat_1(B_43,A_44) != k1_xboole_0
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_16,plain,(
    ! [A_9,B_10,C_13] :
      ( ~ r1_xboole_0(A_9,B_10)
      | ~ r2_hidden(C_13,B_10)
      | ~ r2_hidden(C_13,A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_383,plain,(
    ! [C_93,A_94,B_95] :
      ( ~ r2_hidden(C_93,A_94)
      | ~ r2_hidden(C_93,k2_relat_1(B_95))
      | k10_relat_1(B_95,A_94) != k1_xboole_0
      | ~ v1_relat_1(B_95) ) ),
    inference(resolution,[status(thm)],[c_109,c_16])).

tff(c_1060,plain,(
    ! [A_186,B_187,B_188] :
      ( ~ r2_hidden('#skF_4'(A_186,B_187),k2_relat_1(B_188))
      | k10_relat_1(B_188,B_187) != k1_xboole_0
      | ~ v1_relat_1(B_188)
      | r1_xboole_0(A_186,B_187) ) ),
    inference(resolution,[status(thm)],[c_18,c_383])).

tff(c_1067,plain,(
    ! [B_165,A_164] :
      ( k10_relat_1('#skF_6',B_165) != k1_xboole_0
      | ~ v1_relat_1('#skF_6')
      | ~ r1_tarski(B_165,'#skF_5')
      | r1_xboole_0(A_164,B_165) ) ),
    inference(resolution,[status(thm)],[c_968,c_1060])).

tff(c_1092,plain,(
    ! [B_189,A_190] :
      ( k10_relat_1('#skF_6',B_189) != k1_xboole_0
      | ~ r1_tarski(B_189,'#skF_5')
      | r1_xboole_0(A_190,B_189) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1067])).

tff(c_24,plain,(
    ! [A_15,B_16] :
      ( ~ r2_hidden(A_15,B_16)
      | ~ r1_xboole_0(k1_tarski(A_15),B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1106,plain,(
    ! [A_191,B_192] :
      ( ~ r2_hidden(A_191,B_192)
      | k10_relat_1('#skF_6',B_192) != k1_xboole_0
      | ~ r1_tarski(B_192,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1092,c_24])).

tff(c_1211,plain,(
    ! [B_193] :
      ( k10_relat_1('#skF_6',B_193) != k1_xboole_0
      | ~ r1_tarski(B_193,'#skF_5')
      | k1_xboole_0 = B_193 ) ),
    inference(resolution,[status(thm)],[c_329,c_1106])).

tff(c_1219,plain,
    ( k10_relat_1('#skF_6','#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_73,c_1211])).

tff(c_1226,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1219])).

tff(c_1228,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_1226])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:35:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.30/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.30/1.51  
% 3.30/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.30/1.51  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4
% 3.30/1.51  
% 3.30/1.51  %Foreground sorts:
% 3.30/1.51  
% 3.30/1.51  
% 3.30/1.51  %Background operators:
% 3.30/1.51  
% 3.30/1.51  
% 3.30/1.51  %Foreground operators:
% 3.30/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.30/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.30/1.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.30/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.30/1.51  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.30/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.30/1.51  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.30/1.51  tff('#skF_5', type, '#skF_5': $i).
% 3.30/1.51  tff('#skF_6', type, '#skF_6': $i).
% 3.30/1.51  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.30/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.30/1.51  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.30/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.30/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.30/1.51  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.30/1.51  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.30/1.51  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.30/1.51  
% 3.30/1.53  tff(f_81, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_relat_1)).
% 3.30/1.53  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.30/1.53  tff(f_39, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 3.30/1.53  tff(f_59, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.30/1.53  tff(f_64, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 3.30/1.53  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.30/1.53  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 3.30/1.53  tff(c_34, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.30/1.53  tff(c_30, plain, (k10_relat_1('#skF_6', '#skF_5')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.30/1.53  tff(c_64, plain, (![A_30, B_31]: (r2_hidden('#skF_1'(A_30, B_31), A_30) | r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.30/1.53  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.30/1.53  tff(c_73, plain, (![A_30]: (r1_tarski(A_30, A_30))), inference(resolution, [status(thm)], [c_64, c_4])).
% 3.30/1.53  tff(c_295, plain, (![A_82, B_83]: (r2_hidden('#skF_2'(A_82, B_83), B_83) | r2_hidden('#skF_3'(A_82, B_83), A_82) | B_83=A_82)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.30/1.53  tff(c_22, plain, (![A_14]: (r1_xboole_0(A_14, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.30/1.53  tff(c_42, plain, (![A_20, B_21]: (~r2_hidden(A_20, B_21) | ~r1_xboole_0(k1_tarski(A_20), B_21))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.30/1.53  tff(c_47, plain, (![A_20]: (~r2_hidden(A_20, k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_42])).
% 3.30/1.53  tff(c_329, plain, (![B_83]: (r2_hidden('#skF_2'(k1_xboole_0, B_83), B_83) | k1_xboole_0=B_83)), inference(resolution, [status(thm)], [c_295, c_47])).
% 3.30/1.53  tff(c_36, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.30/1.53  tff(c_32, plain, (r1_tarski('#skF_5', k2_relat_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.30/1.53  tff(c_18, plain, (![A_9, B_10]: (r2_hidden('#skF_4'(A_9, B_10), B_10) | r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.30/1.53  tff(c_84, plain, (![C_37, B_38, A_39]: (r2_hidden(C_37, B_38) | ~r2_hidden(C_37, A_39) | ~r1_tarski(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.30/1.53  tff(c_202, plain, (![A_70, B_71, B_72]: (r2_hidden('#skF_4'(A_70, B_71), B_72) | ~r1_tarski(B_71, B_72) | r1_xboole_0(A_70, B_71))), inference(resolution, [status(thm)], [c_18, c_84])).
% 3.30/1.53  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.30/1.53  tff(c_959, plain, (![A_164, B_165, B_166, B_167]: (r2_hidden('#skF_4'(A_164, B_165), B_166) | ~r1_tarski(B_167, B_166) | ~r1_tarski(B_165, B_167) | r1_xboole_0(A_164, B_165))), inference(resolution, [status(thm)], [c_202, c_2])).
% 3.30/1.53  tff(c_968, plain, (![A_164, B_165]: (r2_hidden('#skF_4'(A_164, B_165), k2_relat_1('#skF_6')) | ~r1_tarski(B_165, '#skF_5') | r1_xboole_0(A_164, B_165))), inference(resolution, [status(thm)], [c_32, c_959])).
% 3.30/1.53  tff(c_109, plain, (![B_43, A_44]: (r1_xboole_0(k2_relat_1(B_43), A_44) | k10_relat_1(B_43, A_44)!=k1_xboole_0 | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.30/1.53  tff(c_16, plain, (![A_9, B_10, C_13]: (~r1_xboole_0(A_9, B_10) | ~r2_hidden(C_13, B_10) | ~r2_hidden(C_13, A_9))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.30/1.53  tff(c_383, plain, (![C_93, A_94, B_95]: (~r2_hidden(C_93, A_94) | ~r2_hidden(C_93, k2_relat_1(B_95)) | k10_relat_1(B_95, A_94)!=k1_xboole_0 | ~v1_relat_1(B_95))), inference(resolution, [status(thm)], [c_109, c_16])).
% 3.30/1.53  tff(c_1060, plain, (![A_186, B_187, B_188]: (~r2_hidden('#skF_4'(A_186, B_187), k2_relat_1(B_188)) | k10_relat_1(B_188, B_187)!=k1_xboole_0 | ~v1_relat_1(B_188) | r1_xboole_0(A_186, B_187))), inference(resolution, [status(thm)], [c_18, c_383])).
% 3.30/1.53  tff(c_1067, plain, (![B_165, A_164]: (k10_relat_1('#skF_6', B_165)!=k1_xboole_0 | ~v1_relat_1('#skF_6') | ~r1_tarski(B_165, '#skF_5') | r1_xboole_0(A_164, B_165))), inference(resolution, [status(thm)], [c_968, c_1060])).
% 3.30/1.53  tff(c_1092, plain, (![B_189, A_190]: (k10_relat_1('#skF_6', B_189)!=k1_xboole_0 | ~r1_tarski(B_189, '#skF_5') | r1_xboole_0(A_190, B_189))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1067])).
% 3.30/1.53  tff(c_24, plain, (![A_15, B_16]: (~r2_hidden(A_15, B_16) | ~r1_xboole_0(k1_tarski(A_15), B_16))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.30/1.53  tff(c_1106, plain, (![A_191, B_192]: (~r2_hidden(A_191, B_192) | k10_relat_1('#skF_6', B_192)!=k1_xboole_0 | ~r1_tarski(B_192, '#skF_5'))), inference(resolution, [status(thm)], [c_1092, c_24])).
% 3.30/1.53  tff(c_1211, plain, (![B_193]: (k10_relat_1('#skF_6', B_193)!=k1_xboole_0 | ~r1_tarski(B_193, '#skF_5') | k1_xboole_0=B_193)), inference(resolution, [status(thm)], [c_329, c_1106])).
% 3.30/1.53  tff(c_1219, plain, (k10_relat_1('#skF_6', '#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_73, c_1211])).
% 3.30/1.53  tff(c_1226, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1219])).
% 3.30/1.53  tff(c_1228, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_1226])).
% 3.30/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.30/1.53  
% 3.30/1.53  Inference rules
% 3.30/1.53  ----------------------
% 3.30/1.53  #Ref     : 0
% 3.30/1.53  #Sup     : 271
% 3.30/1.53  #Fact    : 0
% 3.30/1.53  #Define  : 0
% 3.30/1.53  #Split   : 3
% 3.30/1.53  #Chain   : 0
% 3.30/1.53  #Close   : 0
% 3.30/1.53  
% 3.30/1.53  Ordering : KBO
% 3.30/1.53  
% 3.30/1.53  Simplification rules
% 3.30/1.53  ----------------------
% 3.30/1.53  #Subsume      : 92
% 3.30/1.53  #Demod        : 23
% 3.30/1.53  #Tautology    : 28
% 3.30/1.53  #SimpNegUnit  : 3
% 3.30/1.53  #BackRed      : 0
% 3.30/1.53  
% 3.30/1.53  #Partial instantiations: 0
% 3.30/1.53  #Strategies tried      : 1
% 3.30/1.53  
% 3.30/1.53  Timing (in seconds)
% 3.30/1.53  ----------------------
% 3.30/1.53  Preprocessing        : 0.28
% 3.30/1.53  Parsing              : 0.15
% 3.30/1.53  CNF conversion       : 0.02
% 3.30/1.53  Main loop            : 0.50
% 3.30/1.53  Inferencing          : 0.18
% 3.30/1.53  Reduction            : 0.12
% 3.30/1.53  Demodulation         : 0.08
% 3.30/1.53  BG Simplification    : 0.02
% 3.30/1.53  Subsumption          : 0.15
% 3.30/1.53  Abstraction          : 0.02
% 3.30/1.53  MUC search           : 0.00
% 3.30/1.53  Cooper               : 0.00
% 3.30/1.53  Total                : 0.81
% 3.30/1.53  Index Insertion      : 0.00
% 3.30/1.53  Index Deletion       : 0.00
% 3.30/1.53  Index Matching       : 0.00
% 3.30/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
