%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:27 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :   68 (  82 expanded)
%              Number of leaves         :   35 (  44 expanded)
%              Depth                    :    8
%              Number of atoms          :   78 ( 118 expanded)
%              Number of equality atoms :    5 (   6 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_88,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r2_hidden(k4_tarski(A,B),C)
         => ( r2_hidden(A,k3_relat_1(C))
            & r2_hidden(B,k3_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_34,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_79,axiom,(
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

tff(f_67,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_42,plain,
    ( ~ r2_hidden('#skF_3',k3_relat_1('#skF_4'))
    | ~ r2_hidden('#skF_2',k3_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_75,plain,(
    ~ r2_hidden('#skF_2',k3_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_46,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_178,plain,(
    ! [A_104] :
      ( k2_xboole_0(k1_relat_1(A_104),k2_relat_1(A_104)) = k3_relat_1(A_104)
      | ~ v1_relat_1(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_8,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_199,plain,(
    ! [A_104] :
      ( r1_tarski(k1_relat_1(A_104),k3_relat_1(A_104))
      | ~ v1_relat_1(A_104) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_8])).

tff(c_44,plain,(
    r2_hidden(k4_tarski('#skF_2','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_433,plain,(
    ! [A_150,C_151,B_152] :
      ( r2_hidden(A_150,k1_relat_1(C_151))
      | ~ r2_hidden(k4_tarski(A_150,B_152),C_151)
      | ~ v1_relat_1(C_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_482,plain,
    ( r2_hidden('#skF_2',k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_433])).

tff(c_497,plain,(
    r2_hidden('#skF_2',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_482])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_508,plain,(
    ! [B_153] :
      ( r2_hidden('#skF_2',B_153)
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_153) ) ),
    inference(resolution,[status(thm)],[c_497,c_2])).

tff(c_512,plain,
    ( r2_hidden('#skF_2',k3_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_199,c_508])).

tff(c_527,plain,(
    r2_hidden('#skF_2',k3_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_512])).

tff(c_529,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_527])).

tff(c_530,plain,(
    ~ r2_hidden('#skF_3',k3_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_626,plain,(
    ! [A_194] :
      ( k2_xboole_0(k1_relat_1(A_194),k2_relat_1(A_194)) = k3_relat_1(A_194)
      | ~ v1_relat_1(A_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_22,plain,(
    ! [A_35,B_36] : k3_tarski(k2_tarski(A_35,B_36)) = k2_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_24,plain,(
    ! [A_37] : r1_tarski(A_37,k1_zfmisc_1(k3_tarski(A_37))) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_536,plain,(
    ! [B_154,C_155,A_156] :
      ( r2_hidden(B_154,C_155)
      | ~ r1_tarski(k2_tarski(A_156,B_154),C_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_540,plain,(
    ! [B_154,A_156] : r2_hidden(B_154,k1_zfmisc_1(k3_tarski(k2_tarski(A_156,B_154)))) ),
    inference(resolution,[status(thm)],[c_24,c_536])).

tff(c_548,plain,(
    ! [B_157,A_158] : r2_hidden(B_157,k1_zfmisc_1(k2_xboole_0(A_158,B_157))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_540])).

tff(c_34,plain,(
    ! [A_45,B_46] :
      ( m1_subset_1(A_45,B_46)
      | ~ r2_hidden(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_552,plain,(
    ! [B_157,A_158] : m1_subset_1(B_157,k1_zfmisc_1(k2_xboole_0(A_158,B_157))) ),
    inference(resolution,[status(thm)],[c_548,c_34])).

tff(c_638,plain,(
    ! [A_194] :
      ( m1_subset_1(k2_relat_1(A_194),k1_zfmisc_1(k3_relat_1(A_194)))
      | ~ v1_relat_1(A_194) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_626,c_552])).

tff(c_1231,plain,(
    ! [B_271,C_272,A_273] :
      ( r2_hidden(B_271,k2_relat_1(C_272))
      | ~ r2_hidden(k4_tarski(A_273,B_271),C_272)
      | ~ v1_relat_1(C_272) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1280,plain,
    ( r2_hidden('#skF_3',k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_1231])).

tff(c_1295,plain,(
    r2_hidden('#skF_3',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1280])).

tff(c_32,plain,(
    ! [C_44,A_41,B_42] :
      ( r2_hidden(C_44,A_41)
      | ~ r2_hidden(C_44,B_42)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1365,plain,(
    ! [A_283] :
      ( r2_hidden('#skF_3',A_283)
      | ~ m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1(A_283)) ) ),
    inference(resolution,[status(thm)],[c_1295,c_32])).

tff(c_1377,plain,
    ( r2_hidden('#skF_3',k3_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_638,c_1365])).

tff(c_1390,plain,(
    r2_hidden('#skF_3',k3_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1377])).

tff(c_1392,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_530,c_1390])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:34:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.53/1.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.66  
% 3.53/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.67  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.53/1.67  
% 3.53/1.67  %Foreground sorts:
% 3.53/1.67  
% 3.53/1.67  
% 3.53/1.67  %Background operators:
% 3.53/1.67  
% 3.53/1.67  
% 3.53/1.67  %Foreground operators:
% 3.53/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.53/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.53/1.67  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.53/1.67  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.53/1.67  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 3.53/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.53/1.67  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.53/1.67  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.53/1.67  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.53/1.67  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.53/1.67  tff('#skF_2', type, '#skF_2': $i).
% 3.53/1.67  tff('#skF_3', type, '#skF_3': $i).
% 3.53/1.67  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.53/1.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.53/1.67  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.53/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.53/1.67  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.53/1.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.53/1.67  tff('#skF_4', type, '#skF_4': $i).
% 3.53/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.53/1.67  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.53/1.67  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.53/1.67  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.53/1.67  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.53/1.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.53/1.67  
% 3.53/1.68  tff(f_88, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k3_relat_1(C)) & r2_hidden(B, k3_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_relat_1)).
% 3.53/1.68  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 3.53/1.68  tff(f_34, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.53/1.68  tff(f_79, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 3.53/1.68  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.53/1.68  tff(f_48, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.53/1.68  tff(f_50, axiom, (![A]: r1_tarski(A, k1_zfmisc_1(k3_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 3.53/1.68  tff(f_56, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.53/1.68  tff(f_67, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 3.53/1.68  tff(f_63, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 3.53/1.68  tff(c_42, plain, (~r2_hidden('#skF_3', k3_relat_1('#skF_4')) | ~r2_hidden('#skF_2', k3_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.53/1.68  tff(c_75, plain, (~r2_hidden('#skF_2', k3_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_42])).
% 3.53/1.68  tff(c_46, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.53/1.68  tff(c_178, plain, (![A_104]: (k2_xboole_0(k1_relat_1(A_104), k2_relat_1(A_104))=k3_relat_1(A_104) | ~v1_relat_1(A_104))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.53/1.68  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.53/1.68  tff(c_199, plain, (![A_104]: (r1_tarski(k1_relat_1(A_104), k3_relat_1(A_104)) | ~v1_relat_1(A_104))), inference(superposition, [status(thm), theory('equality')], [c_178, c_8])).
% 3.53/1.68  tff(c_44, plain, (r2_hidden(k4_tarski('#skF_2', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.53/1.68  tff(c_433, plain, (![A_150, C_151, B_152]: (r2_hidden(A_150, k1_relat_1(C_151)) | ~r2_hidden(k4_tarski(A_150, B_152), C_151) | ~v1_relat_1(C_151))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.53/1.68  tff(c_482, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_433])).
% 3.53/1.68  tff(c_497, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_482])).
% 3.53/1.68  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.53/1.68  tff(c_508, plain, (![B_153]: (r2_hidden('#skF_2', B_153) | ~r1_tarski(k1_relat_1('#skF_4'), B_153))), inference(resolution, [status(thm)], [c_497, c_2])).
% 3.53/1.68  tff(c_512, plain, (r2_hidden('#skF_2', k3_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_199, c_508])).
% 3.53/1.68  tff(c_527, plain, (r2_hidden('#skF_2', k3_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_512])).
% 3.53/1.68  tff(c_529, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75, c_527])).
% 3.53/1.68  tff(c_530, plain, (~r2_hidden('#skF_3', k3_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_42])).
% 3.53/1.68  tff(c_626, plain, (![A_194]: (k2_xboole_0(k1_relat_1(A_194), k2_relat_1(A_194))=k3_relat_1(A_194) | ~v1_relat_1(A_194))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.53/1.68  tff(c_22, plain, (![A_35, B_36]: (k3_tarski(k2_tarski(A_35, B_36))=k2_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.53/1.68  tff(c_24, plain, (![A_37]: (r1_tarski(A_37, k1_zfmisc_1(k3_tarski(A_37))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.53/1.68  tff(c_536, plain, (![B_154, C_155, A_156]: (r2_hidden(B_154, C_155) | ~r1_tarski(k2_tarski(A_156, B_154), C_155))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.53/1.68  tff(c_540, plain, (![B_154, A_156]: (r2_hidden(B_154, k1_zfmisc_1(k3_tarski(k2_tarski(A_156, B_154)))))), inference(resolution, [status(thm)], [c_24, c_536])).
% 3.53/1.68  tff(c_548, plain, (![B_157, A_158]: (r2_hidden(B_157, k1_zfmisc_1(k2_xboole_0(A_158, B_157))))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_540])).
% 3.53/1.68  tff(c_34, plain, (![A_45, B_46]: (m1_subset_1(A_45, B_46) | ~r2_hidden(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.53/1.68  tff(c_552, plain, (![B_157, A_158]: (m1_subset_1(B_157, k1_zfmisc_1(k2_xboole_0(A_158, B_157))))), inference(resolution, [status(thm)], [c_548, c_34])).
% 3.53/1.68  tff(c_638, plain, (![A_194]: (m1_subset_1(k2_relat_1(A_194), k1_zfmisc_1(k3_relat_1(A_194))) | ~v1_relat_1(A_194))), inference(superposition, [status(thm), theory('equality')], [c_626, c_552])).
% 3.53/1.68  tff(c_1231, plain, (![B_271, C_272, A_273]: (r2_hidden(B_271, k2_relat_1(C_272)) | ~r2_hidden(k4_tarski(A_273, B_271), C_272) | ~v1_relat_1(C_272))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.53/1.68  tff(c_1280, plain, (r2_hidden('#skF_3', k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_1231])).
% 3.53/1.68  tff(c_1295, plain, (r2_hidden('#skF_3', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1280])).
% 3.53/1.68  tff(c_32, plain, (![C_44, A_41, B_42]: (r2_hidden(C_44, A_41) | ~r2_hidden(C_44, B_42) | ~m1_subset_1(B_42, k1_zfmisc_1(A_41)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.53/1.68  tff(c_1365, plain, (![A_283]: (r2_hidden('#skF_3', A_283) | ~m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1(A_283)))), inference(resolution, [status(thm)], [c_1295, c_32])).
% 3.53/1.68  tff(c_1377, plain, (r2_hidden('#skF_3', k3_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_638, c_1365])).
% 3.53/1.68  tff(c_1390, plain, (r2_hidden('#skF_3', k3_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1377])).
% 3.53/1.68  tff(c_1392, plain, $false, inference(negUnitSimplification, [status(thm)], [c_530, c_1390])).
% 3.53/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.68  
% 3.53/1.68  Inference rules
% 3.53/1.68  ----------------------
% 3.53/1.68  #Ref     : 0
% 3.53/1.68  #Sup     : 311
% 3.53/1.68  #Fact    : 0
% 3.53/1.68  #Define  : 0
% 3.53/1.68  #Split   : 1
% 3.53/1.68  #Chain   : 0
% 3.53/1.68  #Close   : 0
% 3.53/1.68  
% 3.53/1.68  Ordering : KBO
% 3.53/1.68  
% 3.53/1.68  Simplification rules
% 3.53/1.68  ----------------------
% 3.53/1.68  #Subsume      : 9
% 3.53/1.68  #Demod        : 31
% 3.53/1.68  #Tautology    : 35
% 3.53/1.68  #SimpNegUnit  : 2
% 3.53/1.68  #BackRed      : 0
% 3.53/1.68  
% 3.53/1.68  #Partial instantiations: 0
% 3.53/1.68  #Strategies tried      : 1
% 3.53/1.68  
% 3.53/1.68  Timing (in seconds)
% 3.53/1.68  ----------------------
% 3.53/1.68  Preprocessing        : 0.35
% 3.53/1.68  Parsing              : 0.19
% 3.53/1.68  CNF conversion       : 0.02
% 3.53/1.68  Main loop            : 0.51
% 3.53/1.68  Inferencing          : 0.20
% 3.53/1.68  Reduction            : 0.16
% 3.53/1.68  Demodulation         : 0.12
% 3.53/1.68  BG Simplification    : 0.02
% 3.53/1.68  Subsumption          : 0.09
% 3.53/1.68  Abstraction          : 0.02
% 3.53/1.68  MUC search           : 0.00
% 3.53/1.68  Cooper               : 0.00
% 3.53/1.68  Total                : 0.89
% 3.53/1.68  Index Insertion      : 0.00
% 3.53/1.68  Index Deletion       : 0.00
% 3.53/1.68  Index Matching       : 0.00
% 3.53/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
