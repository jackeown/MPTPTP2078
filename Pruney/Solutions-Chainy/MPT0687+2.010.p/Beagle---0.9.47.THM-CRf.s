%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:34 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   59 (  75 expanded)
%              Number of leaves         :   29 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :   82 ( 117 expanded)
%              Number of equality atoms :   20 (  32 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k2_relat_1(B))
        <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

tff(f_65,axiom,(
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

tff(f_60,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_51,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & r2_hidden(C,B) )
     => k3_xboole_0(k2_tarski(A,C),B) = k2_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_30,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_32,plain,
    ( k10_relat_1('#skF_4',k1_tarski('#skF_3')) = k1_xboole_0
    | ~ r2_hidden('#skF_3',k2_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_73,plain,(
    ~ r2_hidden('#skF_3',k2_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_38,plain,
    ( r2_hidden('#skF_3',k2_relat_1('#skF_4'))
    | k10_relat_1('#skF_4',k1_tarski('#skF_3')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_90,plain,(
    k10_relat_1('#skF_4',k1_tarski('#skF_3')) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_38])).

tff(c_56,plain,(
    ! [A_37,B_38] :
      ( r1_xboole_0(k1_tarski(A_37),B_38)
      | r2_hidden(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_59,plain,(
    ! [B_38,A_37] :
      ( r1_xboole_0(B_38,k1_tarski(A_37))
      | r2_hidden(A_37,B_38) ) ),
    inference(resolution,[status(thm)],[c_56,c_6])).

tff(c_95,plain,(
    ! [B_53,A_54] :
      ( k10_relat_1(B_53,A_54) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(B_53),A_54)
      | ~ v1_relat_1(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_137,plain,(
    ! [B_65,A_66] :
      ( k10_relat_1(B_65,k1_tarski(A_66)) = k1_xboole_0
      | ~ v1_relat_1(B_65)
      | r2_hidden(A_66,k2_relat_1(B_65)) ) ),
    inference(resolution,[status(thm)],[c_59,c_95])).

tff(c_140,plain,
    ( k10_relat_1('#skF_4',k1_tarski('#skF_3')) = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_137,c_73])).

tff(c_146,plain,(
    k10_relat_1('#skF_4',k1_tarski('#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_140])).

tff(c_148,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_146])).

tff(c_149,plain,(
    k10_relat_1('#skF_4',k1_tarski('#skF_3')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_150,plain,(
    r2_hidden('#skF_3',k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_191,plain,(
    ! [B_79,A_80] :
      ( r1_xboole_0(k2_relat_1(B_79),A_80)
      | k10_relat_1(B_79,A_80) != k1_xboole_0
      | ~ v1_relat_1(B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_194,plain,(
    ! [A_80,B_79] :
      ( r1_xboole_0(A_80,k2_relat_1(B_79))
      | k10_relat_1(B_79,A_80) != k1_xboole_0
      | ~ v1_relat_1(B_79) ) ),
    inference(resolution,[status(thm)],[c_191,c_6])).

tff(c_20,plain,(
    ! [A_22] : ~ v1_xboole_0(k1_tarski(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_12,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_223,plain,(
    ! [A_89,C_90,B_91] :
      ( k3_xboole_0(k2_tarski(A_89,C_90),B_91) = k2_tarski(A_89,C_90)
      | ~ r2_hidden(C_90,B_91)
      | ~ r2_hidden(A_89,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_244,plain,(
    ! [A_12,B_91] :
      ( k3_xboole_0(k1_tarski(A_12),B_91) = k2_tarski(A_12,A_12)
      | ~ r2_hidden(A_12,B_91)
      | ~ r2_hidden(A_12,B_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_223])).

tff(c_254,plain,(
    ! [A_96,B_97] :
      ( k3_xboole_0(k1_tarski(A_96),B_97) = k1_tarski(A_96)
      | ~ r2_hidden(A_96,B_97)
      | ~ r2_hidden(A_96,B_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_244])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_159,plain,(
    ! [A_67,B_68,C_69] :
      ( ~ r1_xboole_0(A_67,B_68)
      | ~ r2_hidden(C_69,k3_xboole_0(A_67,B_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_164,plain,(
    ! [A_67,B_68] :
      ( ~ r1_xboole_0(A_67,B_68)
      | v1_xboole_0(k3_xboole_0(A_67,B_68)) ) ),
    inference(resolution,[status(thm)],[c_4,c_159])).

tff(c_266,plain,(
    ! [A_96,B_97] :
      ( ~ r1_xboole_0(k1_tarski(A_96),B_97)
      | v1_xboole_0(k1_tarski(A_96))
      | ~ r2_hidden(A_96,B_97)
      | ~ r2_hidden(A_96,B_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_164])).

tff(c_276,plain,(
    ! [A_98,B_99] :
      ( ~ r1_xboole_0(k1_tarski(A_98),B_99)
      | ~ r2_hidden(A_98,B_99)
      | ~ r2_hidden(A_98,B_99) ) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_266])).

tff(c_315,plain,(
    ! [A_104,B_105] :
      ( ~ r2_hidden(A_104,k2_relat_1(B_105))
      | k10_relat_1(B_105,k1_tarski(A_104)) != k1_xboole_0
      | ~ v1_relat_1(B_105) ) ),
    inference(resolution,[status(thm)],[c_194,c_276])).

tff(c_321,plain,
    ( k10_relat_1('#skF_4',k1_tarski('#skF_3')) != k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_150,c_315])).

tff(c_330,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_149,c_321])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:11:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.30  
% 2.05/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.30  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.05/1.30  
% 2.05/1.30  %Foreground sorts:
% 2.05/1.30  
% 2.05/1.30  
% 2.05/1.30  %Background operators:
% 2.05/1.30  
% 2.05/1.30  
% 2.05/1.30  %Foreground operators:
% 2.05/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.05/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.05/1.30  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.05/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.05/1.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.05/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.05/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.05/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.05/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.05/1.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.05/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.05/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.30  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.05/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.05/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.05/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.30  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.05/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.05/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.05/1.30  
% 2.05/1.32  tff(f_85, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_1)).
% 2.05/1.32  tff(f_65, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.05/1.32  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.05/1.32  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 2.05/1.32  tff(f_60, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 2.05/1.32  tff(f_51, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.05/1.32  tff(f_71, axiom, (![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k3_xboole_0(k2_tarski(A, C), B) = k2_tarski(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_zfmisc_1)).
% 2.05/1.32  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.05/1.32  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.05/1.32  tff(c_30, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.05/1.32  tff(c_32, plain, (k10_relat_1('#skF_4', k1_tarski('#skF_3'))=k1_xboole_0 | ~r2_hidden('#skF_3', k2_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.05/1.32  tff(c_73, plain, (~r2_hidden('#skF_3', k2_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_32])).
% 2.05/1.32  tff(c_38, plain, (r2_hidden('#skF_3', k2_relat_1('#skF_4')) | k10_relat_1('#skF_4', k1_tarski('#skF_3'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.05/1.32  tff(c_90, plain, (k10_relat_1('#skF_4', k1_tarski('#skF_3'))!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_73, c_38])).
% 2.05/1.32  tff(c_56, plain, (![A_37, B_38]: (r1_xboole_0(k1_tarski(A_37), B_38) | r2_hidden(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.05/1.32  tff(c_6, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.05/1.32  tff(c_59, plain, (![B_38, A_37]: (r1_xboole_0(B_38, k1_tarski(A_37)) | r2_hidden(A_37, B_38))), inference(resolution, [status(thm)], [c_56, c_6])).
% 2.05/1.32  tff(c_95, plain, (![B_53, A_54]: (k10_relat_1(B_53, A_54)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(B_53), A_54) | ~v1_relat_1(B_53))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.05/1.32  tff(c_137, plain, (![B_65, A_66]: (k10_relat_1(B_65, k1_tarski(A_66))=k1_xboole_0 | ~v1_relat_1(B_65) | r2_hidden(A_66, k2_relat_1(B_65)))), inference(resolution, [status(thm)], [c_59, c_95])).
% 2.05/1.32  tff(c_140, plain, (k10_relat_1('#skF_4', k1_tarski('#skF_3'))=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_137, c_73])).
% 2.05/1.32  tff(c_146, plain, (k10_relat_1('#skF_4', k1_tarski('#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_140])).
% 2.05/1.32  tff(c_148, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_146])).
% 2.05/1.32  tff(c_149, plain, (k10_relat_1('#skF_4', k1_tarski('#skF_3'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_32])).
% 2.05/1.32  tff(c_150, plain, (r2_hidden('#skF_3', k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_32])).
% 2.05/1.32  tff(c_191, plain, (![B_79, A_80]: (r1_xboole_0(k2_relat_1(B_79), A_80) | k10_relat_1(B_79, A_80)!=k1_xboole_0 | ~v1_relat_1(B_79))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.05/1.32  tff(c_194, plain, (![A_80, B_79]: (r1_xboole_0(A_80, k2_relat_1(B_79)) | k10_relat_1(B_79, A_80)!=k1_xboole_0 | ~v1_relat_1(B_79))), inference(resolution, [status(thm)], [c_191, c_6])).
% 2.05/1.32  tff(c_20, plain, (![A_22]: (~v1_xboole_0(k1_tarski(A_22)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.05/1.32  tff(c_12, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.05/1.32  tff(c_223, plain, (![A_89, C_90, B_91]: (k3_xboole_0(k2_tarski(A_89, C_90), B_91)=k2_tarski(A_89, C_90) | ~r2_hidden(C_90, B_91) | ~r2_hidden(A_89, B_91))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.05/1.32  tff(c_244, plain, (![A_12, B_91]: (k3_xboole_0(k1_tarski(A_12), B_91)=k2_tarski(A_12, A_12) | ~r2_hidden(A_12, B_91) | ~r2_hidden(A_12, B_91))), inference(superposition, [status(thm), theory('equality')], [c_12, c_223])).
% 2.05/1.32  tff(c_254, plain, (![A_96, B_97]: (k3_xboole_0(k1_tarski(A_96), B_97)=k1_tarski(A_96) | ~r2_hidden(A_96, B_97) | ~r2_hidden(A_96, B_97))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_244])).
% 2.05/1.32  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.05/1.32  tff(c_159, plain, (![A_67, B_68, C_69]: (~r1_xboole_0(A_67, B_68) | ~r2_hidden(C_69, k3_xboole_0(A_67, B_68)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.05/1.32  tff(c_164, plain, (![A_67, B_68]: (~r1_xboole_0(A_67, B_68) | v1_xboole_0(k3_xboole_0(A_67, B_68)))), inference(resolution, [status(thm)], [c_4, c_159])).
% 2.05/1.32  tff(c_266, plain, (![A_96, B_97]: (~r1_xboole_0(k1_tarski(A_96), B_97) | v1_xboole_0(k1_tarski(A_96)) | ~r2_hidden(A_96, B_97) | ~r2_hidden(A_96, B_97))), inference(superposition, [status(thm), theory('equality')], [c_254, c_164])).
% 2.05/1.32  tff(c_276, plain, (![A_98, B_99]: (~r1_xboole_0(k1_tarski(A_98), B_99) | ~r2_hidden(A_98, B_99) | ~r2_hidden(A_98, B_99))), inference(negUnitSimplification, [status(thm)], [c_20, c_266])).
% 2.05/1.32  tff(c_315, plain, (![A_104, B_105]: (~r2_hidden(A_104, k2_relat_1(B_105)) | k10_relat_1(B_105, k1_tarski(A_104))!=k1_xboole_0 | ~v1_relat_1(B_105))), inference(resolution, [status(thm)], [c_194, c_276])).
% 2.05/1.32  tff(c_321, plain, (k10_relat_1('#skF_4', k1_tarski('#skF_3'))!=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_150, c_315])).
% 2.05/1.32  tff(c_330, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_149, c_321])).
% 2.05/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.32  
% 2.05/1.32  Inference rules
% 2.05/1.32  ----------------------
% 2.05/1.32  #Ref     : 0
% 2.05/1.32  #Sup     : 63
% 2.05/1.32  #Fact    : 0
% 2.05/1.32  #Define  : 0
% 2.05/1.32  #Split   : 1
% 2.05/1.32  #Chain   : 0
% 2.05/1.32  #Close   : 0
% 2.05/1.32  
% 2.05/1.32  Ordering : KBO
% 2.05/1.32  
% 2.05/1.32  Simplification rules
% 2.05/1.32  ----------------------
% 2.05/1.32  #Subsume      : 6
% 2.05/1.32  #Demod        : 7
% 2.05/1.32  #Tautology    : 31
% 2.05/1.32  #SimpNegUnit  : 4
% 2.05/1.32  #BackRed      : 0
% 2.05/1.32  
% 2.05/1.32  #Partial instantiations: 0
% 2.05/1.32  #Strategies tried      : 1
% 2.05/1.32  
% 2.05/1.32  Timing (in seconds)
% 2.05/1.32  ----------------------
% 2.05/1.32  Preprocessing        : 0.27
% 2.05/1.32  Parsing              : 0.14
% 2.05/1.32  CNF conversion       : 0.02
% 2.05/1.32  Main loop            : 0.20
% 2.05/1.32  Inferencing          : 0.09
% 2.05/1.32  Reduction            : 0.05
% 2.05/1.32  Demodulation         : 0.03
% 2.05/1.32  BG Simplification    : 0.01
% 2.05/1.32  Subsumption          : 0.03
% 2.05/1.32  Abstraction          : 0.01
% 2.05/1.32  MUC search           : 0.00
% 2.05/1.32  Cooper               : 0.00
% 2.05/1.32  Total                : 0.49
% 2.05/1.32  Index Insertion      : 0.00
% 2.05/1.32  Index Deletion       : 0.00
% 2.05/1.32  Index Matching       : 0.00
% 2.05/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
