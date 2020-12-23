%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:27 EST 2020

% Result     : Theorem 3.63s
% Output     : CNFRefutation 3.91s
% Verified   : 
% Statistics : Number of formulae       :   68 (  84 expanded)
%              Number of leaves         :   34 (  44 expanded)
%              Depth                    :    8
%              Number of atoms          :   76 ( 122 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r2_hidden(k4_tarski(A,B),C)
         => ( r2_hidden(A,k3_relat_1(C))
            & r2_hidden(B,k3_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_34,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_48,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_50,axiom,(
    ! [A] : r1_tarski(A,k1_zfmisc_1(k3_tarski(A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_58,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(c_46,plain,
    ( ~ r2_hidden('#skF_3',k3_relat_1('#skF_4'))
    | ~ r2_hidden('#skF_2',k3_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_72,plain,(
    ~ r2_hidden('#skF_2',k3_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_50,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_226,plain,(
    ! [A_98] :
      ( k2_xboole_0(k1_relat_1(A_98),k2_relat_1(A_98)) = k3_relat_1(A_98)
      | ~ v1_relat_1(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_8,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_244,plain,(
    ! [A_98] :
      ( r1_tarski(k1_relat_1(A_98),k3_relat_1(A_98))
      | ~ v1_relat_1(A_98) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_8])).

tff(c_48,plain,(
    r2_hidden(k4_tarski('#skF_2','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_806,plain,(
    ! [A_154,C_155,B_156] :
      ( r2_hidden(A_154,k1_relat_1(C_155))
      | ~ r2_hidden(k4_tarski(A_154,B_156),C_155)
      | ~ v1_relat_1(C_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_868,plain,
    ( r2_hidden('#skF_2',k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_806])).

tff(c_886,plain,(
    r2_hidden('#skF_2',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_868])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_912,plain,(
    ! [B_160] :
      ( r2_hidden('#skF_2',B_160)
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_160) ) ),
    inference(resolution,[status(thm)],[c_886,c_2])).

tff(c_916,plain,
    ( r2_hidden('#skF_2',k3_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_244,c_912])).

tff(c_939,plain,(
    r2_hidden('#skF_2',k3_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_916])).

tff(c_941,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_939])).

tff(c_942,plain,(
    ~ r2_hidden('#skF_3',k3_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1226,plain,(
    ! [A_214] :
      ( k2_xboole_0(k1_relat_1(A_214),k2_relat_1(A_214)) = k3_relat_1(A_214)
      | ~ v1_relat_1(A_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_20,plain,(
    ! [A_24,B_25] : k3_tarski(k2_tarski(A_24,B_25)) = k2_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_22,plain,(
    ! [A_26] : r1_tarski(A_26,k1_zfmisc_1(k3_tarski(A_26))) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1016,plain,(
    ! [B_181,C_182,A_183] :
      ( r2_hidden(B_181,C_182)
      | ~ r1_tarski(k2_tarski(A_183,B_181),C_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1024,plain,(
    ! [B_181,A_183] : r2_hidden(B_181,k1_zfmisc_1(k3_tarski(k2_tarski(A_183,B_181)))) ),
    inference(resolution,[status(thm)],[c_22,c_1016])).

tff(c_1033,plain,(
    ! [B_184,A_185] : r2_hidden(B_184,k1_zfmisc_1(k2_xboole_0(A_185,B_184))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1024])).

tff(c_30,plain,(
    ! [A_30] : k3_tarski(k1_zfmisc_1(A_30)) = A_30 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_68,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(A_48,k3_tarski(B_49))
      | ~ r2_hidden(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_71,plain,(
    ! [A_48,A_30] :
      ( r1_tarski(A_48,A_30)
      | ~ r2_hidden(A_48,k1_zfmisc_1(A_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_68])).

tff(c_1037,plain,(
    ! [B_184,A_185] : r1_tarski(B_184,k2_xboole_0(A_185,B_184)) ),
    inference(resolution,[status(thm)],[c_1033,c_71])).

tff(c_1235,plain,(
    ! [A_214] :
      ( r1_tarski(k2_relat_1(A_214),k3_relat_1(A_214))
      | ~ v1_relat_1(A_214) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1226,c_1037])).

tff(c_1829,plain,(
    ! [B_268,C_269,A_270] :
      ( r2_hidden(B_268,k2_relat_1(C_269))
      | ~ r2_hidden(k4_tarski(A_270,B_268),C_269)
      | ~ v1_relat_1(C_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1887,plain,
    ( r2_hidden('#skF_3',k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_1829])).

tff(c_1904,plain,(
    r2_hidden('#skF_3',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1887])).

tff(c_1908,plain,(
    ! [B_271] :
      ( r2_hidden('#skF_3',B_271)
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_271) ) ),
    inference(resolution,[status(thm)],[c_1904,c_2])).

tff(c_1912,plain,
    ( r2_hidden('#skF_3',k3_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1235,c_1908])).

tff(c_1935,plain,(
    r2_hidden('#skF_3',k3_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1912])).

tff(c_1937,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_942,c_1935])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:56:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.63/1.74  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.63/1.75  
% 3.63/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.63/1.75  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.63/1.75  
% 3.63/1.75  %Foreground sorts:
% 3.63/1.75  
% 3.63/1.75  
% 3.63/1.75  %Background operators:
% 3.63/1.75  
% 3.63/1.75  
% 3.63/1.75  %Foreground operators:
% 3.63/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.63/1.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.63/1.75  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.63/1.75  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.63/1.75  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 3.63/1.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.63/1.75  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.63/1.75  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.63/1.75  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.63/1.75  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.63/1.75  tff('#skF_2', type, '#skF_2': $i).
% 3.63/1.75  tff('#skF_3', type, '#skF_3': $i).
% 3.63/1.75  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.63/1.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.63/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.63/1.75  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.63/1.75  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.63/1.75  tff('#skF_4', type, '#skF_4': $i).
% 3.63/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.63/1.75  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.63/1.75  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.63/1.75  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.63/1.75  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.63/1.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.63/1.75  
% 3.91/1.76  tff(f_92, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k3_relat_1(C)) & r2_hidden(B, k3_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_relat_1)).
% 3.91/1.76  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 3.91/1.76  tff(f_34, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.91/1.76  tff(f_83, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 3.91/1.76  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.91/1.76  tff(f_48, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.91/1.76  tff(f_50, axiom, (![A]: r1_tarski(A, k1_zfmisc_1(k3_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 3.91/1.76  tff(f_56, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.91/1.76  tff(f_58, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 3.91/1.76  tff(f_46, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 3.91/1.76  tff(c_46, plain, (~r2_hidden('#skF_3', k3_relat_1('#skF_4')) | ~r2_hidden('#skF_2', k3_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.91/1.76  tff(c_72, plain, (~r2_hidden('#skF_2', k3_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_46])).
% 3.91/1.76  tff(c_50, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.91/1.76  tff(c_226, plain, (![A_98]: (k2_xboole_0(k1_relat_1(A_98), k2_relat_1(A_98))=k3_relat_1(A_98) | ~v1_relat_1(A_98))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.91/1.76  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.91/1.76  tff(c_244, plain, (![A_98]: (r1_tarski(k1_relat_1(A_98), k3_relat_1(A_98)) | ~v1_relat_1(A_98))), inference(superposition, [status(thm), theory('equality')], [c_226, c_8])).
% 3.91/1.76  tff(c_48, plain, (r2_hidden(k4_tarski('#skF_2', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.91/1.76  tff(c_806, plain, (![A_154, C_155, B_156]: (r2_hidden(A_154, k1_relat_1(C_155)) | ~r2_hidden(k4_tarski(A_154, B_156), C_155) | ~v1_relat_1(C_155))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.91/1.76  tff(c_868, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_806])).
% 3.91/1.76  tff(c_886, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_868])).
% 3.91/1.76  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.91/1.76  tff(c_912, plain, (![B_160]: (r2_hidden('#skF_2', B_160) | ~r1_tarski(k1_relat_1('#skF_4'), B_160))), inference(resolution, [status(thm)], [c_886, c_2])).
% 3.91/1.76  tff(c_916, plain, (r2_hidden('#skF_2', k3_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_244, c_912])).
% 3.91/1.76  tff(c_939, plain, (r2_hidden('#skF_2', k3_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_916])).
% 3.91/1.76  tff(c_941, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_939])).
% 3.91/1.76  tff(c_942, plain, (~r2_hidden('#skF_3', k3_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_46])).
% 3.91/1.76  tff(c_1226, plain, (![A_214]: (k2_xboole_0(k1_relat_1(A_214), k2_relat_1(A_214))=k3_relat_1(A_214) | ~v1_relat_1(A_214))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.91/1.76  tff(c_20, plain, (![A_24, B_25]: (k3_tarski(k2_tarski(A_24, B_25))=k2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.91/1.76  tff(c_22, plain, (![A_26]: (r1_tarski(A_26, k1_zfmisc_1(k3_tarski(A_26))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.91/1.76  tff(c_1016, plain, (![B_181, C_182, A_183]: (r2_hidden(B_181, C_182) | ~r1_tarski(k2_tarski(A_183, B_181), C_182))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.91/1.76  tff(c_1024, plain, (![B_181, A_183]: (r2_hidden(B_181, k1_zfmisc_1(k3_tarski(k2_tarski(A_183, B_181)))))), inference(resolution, [status(thm)], [c_22, c_1016])).
% 3.91/1.76  tff(c_1033, plain, (![B_184, A_185]: (r2_hidden(B_184, k1_zfmisc_1(k2_xboole_0(A_185, B_184))))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1024])).
% 3.91/1.76  tff(c_30, plain, (![A_30]: (k3_tarski(k1_zfmisc_1(A_30))=A_30)), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.91/1.76  tff(c_68, plain, (![A_48, B_49]: (r1_tarski(A_48, k3_tarski(B_49)) | ~r2_hidden(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.91/1.76  tff(c_71, plain, (![A_48, A_30]: (r1_tarski(A_48, A_30) | ~r2_hidden(A_48, k1_zfmisc_1(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_68])).
% 3.91/1.76  tff(c_1037, plain, (![B_184, A_185]: (r1_tarski(B_184, k2_xboole_0(A_185, B_184)))), inference(resolution, [status(thm)], [c_1033, c_71])).
% 3.91/1.76  tff(c_1235, plain, (![A_214]: (r1_tarski(k2_relat_1(A_214), k3_relat_1(A_214)) | ~v1_relat_1(A_214))), inference(superposition, [status(thm), theory('equality')], [c_1226, c_1037])).
% 3.91/1.76  tff(c_1829, plain, (![B_268, C_269, A_270]: (r2_hidden(B_268, k2_relat_1(C_269)) | ~r2_hidden(k4_tarski(A_270, B_268), C_269) | ~v1_relat_1(C_269))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.91/1.76  tff(c_1887, plain, (r2_hidden('#skF_3', k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_1829])).
% 3.91/1.76  tff(c_1904, plain, (r2_hidden('#skF_3', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1887])).
% 3.91/1.76  tff(c_1908, plain, (![B_271]: (r2_hidden('#skF_3', B_271) | ~r1_tarski(k2_relat_1('#skF_4'), B_271))), inference(resolution, [status(thm)], [c_1904, c_2])).
% 3.91/1.76  tff(c_1912, plain, (r2_hidden('#skF_3', k3_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1235, c_1908])).
% 3.91/1.76  tff(c_1935, plain, (r2_hidden('#skF_3', k3_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1912])).
% 3.91/1.76  tff(c_1937, plain, $false, inference(negUnitSimplification, [status(thm)], [c_942, c_1935])).
% 3.91/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.91/1.76  
% 3.91/1.76  Inference rules
% 3.91/1.76  ----------------------
% 3.91/1.76  #Ref     : 0
% 3.91/1.76  #Sup     : 395
% 3.91/1.76  #Fact    : 0
% 3.91/1.76  #Define  : 0
% 3.91/1.76  #Split   : 3
% 3.91/1.76  #Chain   : 0
% 3.91/1.76  #Close   : 0
% 3.91/1.76  
% 3.91/1.76  Ordering : KBO
% 3.91/1.76  
% 3.91/1.76  Simplification rules
% 3.91/1.76  ----------------------
% 3.91/1.76  #Subsume      : 12
% 3.91/1.76  #Demod        : 95
% 3.91/1.76  #Tautology    : 75
% 3.91/1.76  #SimpNegUnit  : 5
% 3.91/1.76  #BackRed      : 0
% 3.91/1.76  
% 3.91/1.76  #Partial instantiations: 0
% 3.91/1.76  #Strategies tried      : 1
% 3.91/1.76  
% 3.91/1.76  Timing (in seconds)
% 3.91/1.76  ----------------------
% 3.95/1.77  Preprocessing        : 0.30
% 3.95/1.77  Parsing              : 0.16
% 3.95/1.77  CNF conversion       : 0.02
% 3.95/1.77  Main loop            : 0.62
% 3.95/1.77  Inferencing          : 0.25
% 3.95/1.77  Reduction            : 0.19
% 3.95/1.77  Demodulation         : 0.14
% 3.95/1.77  BG Simplification    : 0.02
% 3.95/1.77  Subsumption          : 0.10
% 3.95/1.77  Abstraction          : 0.03
% 3.95/1.77  MUC search           : 0.00
% 3.95/1.77  Cooper               : 0.00
% 3.95/1.77  Total                : 0.96
% 3.95/1.77  Index Insertion      : 0.00
% 3.95/1.77  Index Deletion       : 0.00
% 3.95/1.77  Index Matching       : 0.00
% 3.95/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
