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
% DateTime   : Thu Dec  3 10:04:34 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 3.10s
% Verified   : 
% Statistics : Number of formulae       :   56 (  78 expanded)
%              Number of leaves         :   27 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :   77 ( 128 expanded)
%              Number of equality atoms :   14 (  25 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k2_relat_1(B))
        <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_66,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_53,axiom,(
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

tff(c_32,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_40,plain,
    ( r2_hidden('#skF_3',k2_relat_1('#skF_4'))
    | k10_relat_1('#skF_4',k1_tarski('#skF_3')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_75,plain,(
    k10_relat_1('#skF_4',k1_tarski('#skF_3')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_58,plain,(
    ! [A_39,B_40] :
      ( r1_xboole_0(k1_tarski(A_39),B_40)
      | r2_hidden(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_61,plain,(
    ! [B_40,A_39] :
      ( r1_xboole_0(B_40,k1_tarski(A_39))
      | r2_hidden(A_39,B_40) ) ),
    inference(resolution,[status(thm)],[c_58,c_6])).

tff(c_124,plain,(
    ! [B_61,A_62] :
      ( k10_relat_1(B_61,A_62) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(B_61),A_62)
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_600,plain,(
    ! [B_110,A_111] :
      ( k10_relat_1(B_110,k1_tarski(A_111)) = k1_xboole_0
      | ~ v1_relat_1(B_110)
      | r2_hidden(A_111,k2_relat_1(B_110)) ) ),
    inference(resolution,[status(thm)],[c_61,c_124])).

tff(c_34,plain,
    ( k10_relat_1('#skF_4',k1_tarski('#skF_3')) = k1_xboole_0
    | ~ r2_hidden('#skF_3',k2_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_116,plain,(
    ~ r2_hidden('#skF_3',k2_relat_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_34])).

tff(c_613,plain,
    ( k10_relat_1('#skF_4',k1_tarski('#skF_3')) = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_600,c_116])).

tff(c_622,plain,(
    k10_relat_1('#skF_4',k1_tarski('#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_613])).

tff(c_624,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_622])).

tff(c_626,plain,(
    k10_relat_1('#skF_4',k1_tarski('#skF_3')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_625,plain,(
    r2_hidden('#skF_3',k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_24,plain,(
    ! [A_27] : ~ v1_xboole_0(k1_tarski(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_655,plain,(
    ! [A_120,B_121,C_122] :
      ( ~ r1_xboole_0(A_120,B_121)
      | ~ r2_hidden(C_122,B_121)
      | ~ r2_hidden(C_122,A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_736,plain,(
    ! [C_141,A_142,B_143] :
      ( ~ r2_hidden(C_141,k1_tarski(A_142))
      | ~ r2_hidden(C_141,B_143)
      | r2_hidden(A_142,B_143) ) ),
    inference(resolution,[status(thm)],[c_61,c_655])).

tff(c_745,plain,(
    ! [A_142,B_143] :
      ( ~ r2_hidden('#skF_1'(k1_tarski(A_142)),B_143)
      | r2_hidden(A_142,B_143)
      | v1_xboole_0(k1_tarski(A_142)) ) ),
    inference(resolution,[status(thm)],[c_4,c_736])).

tff(c_760,plain,(
    ! [A_148,B_149] :
      ( ~ r2_hidden('#skF_1'(k1_tarski(A_148)),B_149)
      | r2_hidden(A_148,B_149) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_745])).

tff(c_764,plain,(
    ! [A_148] :
      ( r2_hidden(A_148,k1_tarski(A_148))
      | v1_xboole_0(k1_tarski(A_148)) ) ),
    inference(resolution,[status(thm)],[c_4,c_760])).

tff(c_767,plain,(
    ! [A_148] : r2_hidden(A_148,k1_tarski(A_148)) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_764])).

tff(c_698,plain,(
    ! [B_131,A_132] :
      ( r1_xboole_0(k2_relat_1(B_131),A_132)
      | k10_relat_1(B_131,A_132) != k1_xboole_0
      | ~ v1_relat_1(B_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_8,plain,(
    ! [A_7,B_8,C_11] :
      ( ~ r1_xboole_0(A_7,B_8)
      | ~ r2_hidden(C_11,B_8)
      | ~ r2_hidden(C_11,A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1166,plain,(
    ! [C_175,A_176,B_177] :
      ( ~ r2_hidden(C_175,A_176)
      | ~ r2_hidden(C_175,k2_relat_1(B_177))
      | k10_relat_1(B_177,A_176) != k1_xboole_0
      | ~ v1_relat_1(B_177) ) ),
    inference(resolution,[status(thm)],[c_698,c_8])).

tff(c_1388,plain,(
    ! [A_185,B_186] :
      ( ~ r2_hidden(A_185,k2_relat_1(B_186))
      | k10_relat_1(B_186,k1_tarski(A_185)) != k1_xboole_0
      | ~ v1_relat_1(B_186) ) ),
    inference(resolution,[status(thm)],[c_767,c_1166])).

tff(c_1433,plain,
    ( k10_relat_1('#skF_4',k1_tarski('#skF_3')) != k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_625,c_1388])).

tff(c_1463,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_626,c_1433])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:47:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.98/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.10/1.46  
% 3.10/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.10/1.47  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 3.10/1.47  
% 3.10/1.47  %Foreground sorts:
% 3.10/1.47  
% 3.10/1.47  
% 3.10/1.47  %Background operators:
% 3.10/1.47  
% 3.10/1.47  
% 3.10/1.47  %Foreground operators:
% 3.10/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.10/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.10/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.10/1.47  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.10/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.10/1.47  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.10/1.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.10/1.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.10/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.10/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.10/1.47  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.10/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.10/1.47  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.10/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.10/1.47  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.10/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.10/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.10/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.10/1.47  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.10/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.10/1.47  
% 3.10/1.48  tff(f_85, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_1)).
% 3.10/1.48  tff(f_71, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.10/1.48  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.10/1.48  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 3.10/1.48  tff(f_66, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 3.10/1.48  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.10/1.48  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.10/1.48  tff(c_32, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.10/1.48  tff(c_40, plain, (r2_hidden('#skF_3', k2_relat_1('#skF_4')) | k10_relat_1('#skF_4', k1_tarski('#skF_3'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.10/1.48  tff(c_75, plain, (k10_relat_1('#skF_4', k1_tarski('#skF_3'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_40])).
% 3.10/1.48  tff(c_58, plain, (![A_39, B_40]: (r1_xboole_0(k1_tarski(A_39), B_40) | r2_hidden(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.10/1.48  tff(c_6, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.10/1.48  tff(c_61, plain, (![B_40, A_39]: (r1_xboole_0(B_40, k1_tarski(A_39)) | r2_hidden(A_39, B_40))), inference(resolution, [status(thm)], [c_58, c_6])).
% 3.10/1.48  tff(c_124, plain, (![B_61, A_62]: (k10_relat_1(B_61, A_62)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(B_61), A_62) | ~v1_relat_1(B_61))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.10/1.48  tff(c_600, plain, (![B_110, A_111]: (k10_relat_1(B_110, k1_tarski(A_111))=k1_xboole_0 | ~v1_relat_1(B_110) | r2_hidden(A_111, k2_relat_1(B_110)))), inference(resolution, [status(thm)], [c_61, c_124])).
% 3.10/1.48  tff(c_34, plain, (k10_relat_1('#skF_4', k1_tarski('#skF_3'))=k1_xboole_0 | ~r2_hidden('#skF_3', k2_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.10/1.48  tff(c_116, plain, (~r2_hidden('#skF_3', k2_relat_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_75, c_34])).
% 3.10/1.48  tff(c_613, plain, (k10_relat_1('#skF_4', k1_tarski('#skF_3'))=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_600, c_116])).
% 3.10/1.48  tff(c_622, plain, (k10_relat_1('#skF_4', k1_tarski('#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_613])).
% 3.10/1.48  tff(c_624, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75, c_622])).
% 3.10/1.48  tff(c_626, plain, (k10_relat_1('#skF_4', k1_tarski('#skF_3'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_40])).
% 3.10/1.48  tff(c_625, plain, (r2_hidden('#skF_3', k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_40])).
% 3.10/1.48  tff(c_24, plain, (![A_27]: (~v1_xboole_0(k1_tarski(A_27)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.10/1.48  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.10/1.48  tff(c_655, plain, (![A_120, B_121, C_122]: (~r1_xboole_0(A_120, B_121) | ~r2_hidden(C_122, B_121) | ~r2_hidden(C_122, A_120))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.10/1.48  tff(c_736, plain, (![C_141, A_142, B_143]: (~r2_hidden(C_141, k1_tarski(A_142)) | ~r2_hidden(C_141, B_143) | r2_hidden(A_142, B_143))), inference(resolution, [status(thm)], [c_61, c_655])).
% 3.10/1.48  tff(c_745, plain, (![A_142, B_143]: (~r2_hidden('#skF_1'(k1_tarski(A_142)), B_143) | r2_hidden(A_142, B_143) | v1_xboole_0(k1_tarski(A_142)))), inference(resolution, [status(thm)], [c_4, c_736])).
% 3.10/1.48  tff(c_760, plain, (![A_148, B_149]: (~r2_hidden('#skF_1'(k1_tarski(A_148)), B_149) | r2_hidden(A_148, B_149))), inference(negUnitSimplification, [status(thm)], [c_24, c_745])).
% 3.10/1.48  tff(c_764, plain, (![A_148]: (r2_hidden(A_148, k1_tarski(A_148)) | v1_xboole_0(k1_tarski(A_148)))), inference(resolution, [status(thm)], [c_4, c_760])).
% 3.10/1.48  tff(c_767, plain, (![A_148]: (r2_hidden(A_148, k1_tarski(A_148)))), inference(negUnitSimplification, [status(thm)], [c_24, c_764])).
% 3.10/1.48  tff(c_698, plain, (![B_131, A_132]: (r1_xboole_0(k2_relat_1(B_131), A_132) | k10_relat_1(B_131, A_132)!=k1_xboole_0 | ~v1_relat_1(B_131))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.10/1.48  tff(c_8, plain, (![A_7, B_8, C_11]: (~r1_xboole_0(A_7, B_8) | ~r2_hidden(C_11, B_8) | ~r2_hidden(C_11, A_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.10/1.48  tff(c_1166, plain, (![C_175, A_176, B_177]: (~r2_hidden(C_175, A_176) | ~r2_hidden(C_175, k2_relat_1(B_177)) | k10_relat_1(B_177, A_176)!=k1_xboole_0 | ~v1_relat_1(B_177))), inference(resolution, [status(thm)], [c_698, c_8])).
% 3.10/1.48  tff(c_1388, plain, (![A_185, B_186]: (~r2_hidden(A_185, k2_relat_1(B_186)) | k10_relat_1(B_186, k1_tarski(A_185))!=k1_xboole_0 | ~v1_relat_1(B_186))), inference(resolution, [status(thm)], [c_767, c_1166])).
% 3.10/1.48  tff(c_1433, plain, (k10_relat_1('#skF_4', k1_tarski('#skF_3'))!=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_625, c_1388])).
% 3.10/1.48  tff(c_1463, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_626, c_1433])).
% 3.10/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.10/1.48  
% 3.10/1.48  Inference rules
% 3.10/1.48  ----------------------
% 3.10/1.48  #Ref     : 0
% 3.10/1.48  #Sup     : 309
% 3.10/1.48  #Fact    : 0
% 3.10/1.48  #Define  : 0
% 3.10/1.48  #Split   : 1
% 3.10/1.48  #Chain   : 0
% 3.10/1.48  #Close   : 0
% 3.10/1.48  
% 3.10/1.48  Ordering : KBO
% 3.10/1.48  
% 3.10/1.48  Simplification rules
% 3.10/1.48  ----------------------
% 3.10/1.48  #Subsume      : 61
% 3.10/1.48  #Demod        : 66
% 3.10/1.48  #Tautology    : 88
% 3.10/1.48  #SimpNegUnit  : 38
% 3.10/1.48  #BackRed      : 0
% 3.10/1.48  
% 3.10/1.48  #Partial instantiations: 0
% 3.10/1.48  #Strategies tried      : 1
% 3.10/1.48  
% 3.10/1.48  Timing (in seconds)
% 3.10/1.48  ----------------------
% 3.10/1.48  Preprocessing        : 0.30
% 3.10/1.48  Parsing              : 0.16
% 3.10/1.48  CNF conversion       : 0.02
% 3.10/1.48  Main loop            : 0.42
% 3.10/1.48  Inferencing          : 0.17
% 3.10/1.48  Reduction            : 0.11
% 3.10/1.48  Demodulation         : 0.07
% 3.10/1.48  BG Simplification    : 0.02
% 3.10/1.48  Subsumption          : 0.08
% 3.10/1.48  Abstraction          : 0.02
% 3.10/1.48  MUC search           : 0.00
% 3.10/1.48  Cooper               : 0.00
% 3.10/1.48  Total                : 0.74
% 3.10/1.48  Index Insertion      : 0.00
% 3.10/1.48  Index Deletion       : 0.00
% 3.10/1.48  Index Matching       : 0.00
% 3.10/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
