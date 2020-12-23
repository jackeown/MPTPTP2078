%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:49 EST 2020

% Result     : Theorem 3.78s
% Output     : CNFRefutation 3.93s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 157 expanded)
%              Number of leaves         :   34 (  68 expanded)
%              Depth                    :    9
%              Number of atoms          :   94 ( 284 expanded)
%              Number of equality atoms :   24 (  79 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_tarski > k1_xboole_0 > #skF_6 > #skF_3 > #skF_9 > #skF_7 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_101,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(B,A)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_91,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_69,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_73,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_65,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_67,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_75,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_60,plain,(
    '#skF_9' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r2_xboole_0(A_6,B_7)
      | B_7 = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_3'(A_13,B_14),B_14)
      | ~ r2_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_66,plain,(
    k2_zfmisc_1('#skF_9','#skF_8') = k2_zfmisc_1('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1681,plain,(
    ! [A_147,B_148,C_149,D_150] :
      ( r2_hidden(k4_tarski(A_147,B_148),k2_zfmisc_1(C_149,D_150))
      | ~ r2_hidden(B_148,D_150)
      | ~ r2_hidden(A_147,C_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1862,plain,(
    ! [A_155,B_156] :
      ( r2_hidden(k4_tarski(A_155,B_156),k2_zfmisc_1('#skF_8','#skF_9'))
      | ~ r2_hidden(B_156,'#skF_8')
      | ~ r2_hidden(A_155,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_1681])).

tff(c_56,plain,(
    ! [A_44,C_46,B_45,D_47] :
      ( r2_hidden(A_44,C_46)
      | ~ r2_hidden(k4_tarski(A_44,B_45),k2_zfmisc_1(C_46,D_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1880,plain,(
    ! [A_155,B_156] :
      ( r2_hidden(A_155,'#skF_8')
      | ~ r2_hidden(B_156,'#skF_8')
      | ~ r2_hidden(A_155,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1862,c_56])).

tff(c_1963,plain,(
    ! [B_160] : ~ r2_hidden(B_160,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1880])).

tff(c_1996,plain,(
    ! [B_161] : r1_tarski('#skF_8',B_161) ),
    inference(resolution,[status(thm)],[c_6,c_1963])).

tff(c_26,plain,(
    ! [A_18] : r1_xboole_0(A_18,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_30,plain,(
    ! [A_22] : k5_xboole_0(A_22,A_22) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_22,plain,(
    ! [A_16] : k2_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_24,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_172,plain,(
    ! [A_80,B_81] : k5_xboole_0(k5_xboole_0(A_80,B_81),k2_xboole_0(A_80,B_81)) = k3_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_190,plain,(
    ! [A_17] : k5_xboole_0(A_17,k2_xboole_0(A_17,k1_xboole_0)) = k3_xboole_0(A_17,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_172])).

tff(c_198,plain,(
    ! [A_82] : k3_xboole_0(A_82,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_22,c_190])).

tff(c_115,plain,(
    ! [A_59,B_60,C_61] :
      ( ~ r1_xboole_0(A_59,B_60)
      | ~ r2_hidden(C_61,k3_xboole_0(A_59,B_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_120,plain,(
    ! [A_59,B_60,A_13] :
      ( ~ r1_xboole_0(A_59,B_60)
      | ~ r2_xboole_0(A_13,k3_xboole_0(A_59,B_60)) ) ),
    inference(resolution,[status(thm)],[c_20,c_115])).

tff(c_206,plain,(
    ! [A_82,A_13] :
      ( ~ r1_xboole_0(A_82,k1_xboole_0)
      | ~ r2_xboole_0(A_13,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_120])).

tff(c_224,plain,(
    ! [A_83] : ~ r2_xboole_0(A_83,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_206])).

tff(c_229,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_224])).

tff(c_2000,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1996,c_229])).

tff(c_2004,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2000])).

tff(c_2006,plain,(
    ! [A_162] :
      ( r2_hidden(A_162,'#skF_8')
      | ~ r2_hidden(A_162,'#skF_9') ) ),
    inference(splitRight,[status(thm)],[c_1880])).

tff(c_2062,plain,(
    ! [A_167] :
      ( r2_hidden('#skF_3'(A_167,'#skF_9'),'#skF_8')
      | ~ r2_xboole_0(A_167,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_20,c_2006])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( ~ r2_hidden('#skF_3'(A_13,B_14),A_13)
      | ~ r2_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2073,plain,(
    ~ r2_xboole_0('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_2062,c_18])).

tff(c_2076,plain,
    ( '#skF_9' = '#skF_8'
    | ~ r1_tarski('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_8,c_2073])).

tff(c_2079,plain,(
    ~ r1_tarski('#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2076])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_54,plain,(
    ! [B_45,D_47,A_44,C_46] :
      ( r2_hidden(B_45,D_47)
      | ~ r2_hidden(k4_tarski(A_44,B_45),k2_zfmisc_1(C_46,D_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1882,plain,(
    ! [B_156,A_155] :
      ( r2_hidden(B_156,'#skF_9')
      | ~ r2_hidden(B_156,'#skF_8')
      | ~ r2_hidden(A_155,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1862,c_54])).

tff(c_2142,plain,(
    ! [A_171] : ~ r2_hidden(A_171,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_1882])).

tff(c_2180,plain,(
    ! [B_175] : r1_tarski('#skF_9',B_175) ),
    inference(resolution,[status(thm)],[c_6,c_2142])).

tff(c_2184,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_2180,c_229])).

tff(c_2188,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_2184])).

tff(c_2190,plain,(
    ! [B_176] :
      ( r2_hidden(B_176,'#skF_9')
      | ~ r2_hidden(B_176,'#skF_8') ) ),
    inference(splitRight,[status(thm)],[c_1882])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2501,plain,(
    ! [A_197] :
      ( r1_tarski(A_197,'#skF_9')
      | ~ r2_hidden('#skF_1'(A_197,'#skF_9'),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_2190,c_4])).

tff(c_2509,plain,(
    r1_tarski('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_6,c_2501])).

tff(c_2515,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2079,c_2079,c_2509])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:36:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.78/1.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.78/1.67  
% 3.78/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.78/1.67  %$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_tarski > k1_xboole_0 > #skF_6 > #skF_3 > #skF_9 > #skF_7 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 3.78/1.67  
% 3.78/1.67  %Foreground sorts:
% 3.78/1.67  
% 3.78/1.67  
% 3.78/1.67  %Background operators:
% 3.78/1.67  
% 3.78/1.67  
% 3.78/1.67  %Foreground operators:
% 3.78/1.67  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.78/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.78/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.78/1.67  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.78/1.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.78/1.67  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.78/1.67  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.78/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.78/1.67  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.78/1.67  tff('#skF_9', type, '#skF_9': $i).
% 3.78/1.67  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 3.78/1.67  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 3.78/1.67  tff('#skF_8', type, '#skF_8': $i).
% 3.78/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.78/1.67  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.78/1.67  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.78/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.78/1.67  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.78/1.67  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.78/1.67  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.78/1.67  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.78/1.67  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.78/1.67  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.78/1.67  
% 3.93/1.68  tff(f_101, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(B, A)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t114_zfmisc_1)).
% 3.93/1.68  tff(f_39, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 3.93/1.68  tff(f_63, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_0)).
% 3.93/1.68  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.93/1.68  tff(f_91, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.93/1.68  tff(f_69, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.93/1.68  tff(f_73, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.93/1.68  tff(f_65, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.93/1.68  tff(f_67, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.93/1.68  tff(f_75, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 3.93/1.68  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.93/1.68  tff(c_60, plain, ('#skF_9'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.93/1.68  tff(c_8, plain, (![A_6, B_7]: (r2_xboole_0(A_6, B_7) | B_7=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.93/1.68  tff(c_20, plain, (![A_13, B_14]: (r2_hidden('#skF_3'(A_13, B_14), B_14) | ~r2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.93/1.68  tff(c_64, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.93/1.68  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.93/1.68  tff(c_66, plain, (k2_zfmisc_1('#skF_9', '#skF_8')=k2_zfmisc_1('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.93/1.68  tff(c_1681, plain, (![A_147, B_148, C_149, D_150]: (r2_hidden(k4_tarski(A_147, B_148), k2_zfmisc_1(C_149, D_150)) | ~r2_hidden(B_148, D_150) | ~r2_hidden(A_147, C_149))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.93/1.68  tff(c_1862, plain, (![A_155, B_156]: (r2_hidden(k4_tarski(A_155, B_156), k2_zfmisc_1('#skF_8', '#skF_9')) | ~r2_hidden(B_156, '#skF_8') | ~r2_hidden(A_155, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_66, c_1681])).
% 3.93/1.68  tff(c_56, plain, (![A_44, C_46, B_45, D_47]: (r2_hidden(A_44, C_46) | ~r2_hidden(k4_tarski(A_44, B_45), k2_zfmisc_1(C_46, D_47)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.93/1.68  tff(c_1880, plain, (![A_155, B_156]: (r2_hidden(A_155, '#skF_8') | ~r2_hidden(B_156, '#skF_8') | ~r2_hidden(A_155, '#skF_9'))), inference(resolution, [status(thm)], [c_1862, c_56])).
% 3.93/1.68  tff(c_1963, plain, (![B_160]: (~r2_hidden(B_160, '#skF_8'))), inference(splitLeft, [status(thm)], [c_1880])).
% 3.93/1.68  tff(c_1996, plain, (![B_161]: (r1_tarski('#skF_8', B_161))), inference(resolution, [status(thm)], [c_6, c_1963])).
% 3.93/1.68  tff(c_26, plain, (![A_18]: (r1_xboole_0(A_18, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.93/1.68  tff(c_30, plain, (![A_22]: (k5_xboole_0(A_22, A_22)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.93/1.68  tff(c_22, plain, (![A_16]: (k2_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.93/1.68  tff(c_24, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=A_17)), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.93/1.68  tff(c_172, plain, (![A_80, B_81]: (k5_xboole_0(k5_xboole_0(A_80, B_81), k2_xboole_0(A_80, B_81))=k3_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.93/1.68  tff(c_190, plain, (![A_17]: (k5_xboole_0(A_17, k2_xboole_0(A_17, k1_xboole_0))=k3_xboole_0(A_17, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_172])).
% 3.93/1.68  tff(c_198, plain, (![A_82]: (k3_xboole_0(A_82, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_22, c_190])).
% 3.93/1.68  tff(c_115, plain, (![A_59, B_60, C_61]: (~r1_xboole_0(A_59, B_60) | ~r2_hidden(C_61, k3_xboole_0(A_59, B_60)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.93/1.68  tff(c_120, plain, (![A_59, B_60, A_13]: (~r1_xboole_0(A_59, B_60) | ~r2_xboole_0(A_13, k3_xboole_0(A_59, B_60)))), inference(resolution, [status(thm)], [c_20, c_115])).
% 3.93/1.68  tff(c_206, plain, (![A_82, A_13]: (~r1_xboole_0(A_82, k1_xboole_0) | ~r2_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_198, c_120])).
% 3.93/1.68  tff(c_224, plain, (![A_83]: (~r2_xboole_0(A_83, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_206])).
% 3.93/1.68  tff(c_229, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_224])).
% 3.93/1.68  tff(c_2000, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_1996, c_229])).
% 3.93/1.68  tff(c_2004, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_2000])).
% 3.93/1.68  tff(c_2006, plain, (![A_162]: (r2_hidden(A_162, '#skF_8') | ~r2_hidden(A_162, '#skF_9'))), inference(splitRight, [status(thm)], [c_1880])).
% 3.93/1.68  tff(c_2062, plain, (![A_167]: (r2_hidden('#skF_3'(A_167, '#skF_9'), '#skF_8') | ~r2_xboole_0(A_167, '#skF_9'))), inference(resolution, [status(thm)], [c_20, c_2006])).
% 3.93/1.68  tff(c_18, plain, (![A_13, B_14]: (~r2_hidden('#skF_3'(A_13, B_14), A_13) | ~r2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.93/1.68  tff(c_2073, plain, (~r2_xboole_0('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_2062, c_18])).
% 3.93/1.68  tff(c_2076, plain, ('#skF_9'='#skF_8' | ~r1_tarski('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_8, c_2073])).
% 3.93/1.68  tff(c_2079, plain, (~r1_tarski('#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_60, c_2076])).
% 3.93/1.68  tff(c_62, plain, (k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.93/1.68  tff(c_54, plain, (![B_45, D_47, A_44, C_46]: (r2_hidden(B_45, D_47) | ~r2_hidden(k4_tarski(A_44, B_45), k2_zfmisc_1(C_46, D_47)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.93/1.68  tff(c_1882, plain, (![B_156, A_155]: (r2_hidden(B_156, '#skF_9') | ~r2_hidden(B_156, '#skF_8') | ~r2_hidden(A_155, '#skF_9'))), inference(resolution, [status(thm)], [c_1862, c_54])).
% 3.93/1.68  tff(c_2142, plain, (![A_171]: (~r2_hidden(A_171, '#skF_9'))), inference(splitLeft, [status(thm)], [c_1882])).
% 3.93/1.68  tff(c_2180, plain, (![B_175]: (r1_tarski('#skF_9', B_175))), inference(resolution, [status(thm)], [c_6, c_2142])).
% 3.93/1.68  tff(c_2184, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_2180, c_229])).
% 3.93/1.68  tff(c_2188, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_2184])).
% 3.93/1.68  tff(c_2190, plain, (![B_176]: (r2_hidden(B_176, '#skF_9') | ~r2_hidden(B_176, '#skF_8'))), inference(splitRight, [status(thm)], [c_1882])).
% 3.93/1.68  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.93/1.68  tff(c_2501, plain, (![A_197]: (r1_tarski(A_197, '#skF_9') | ~r2_hidden('#skF_1'(A_197, '#skF_9'), '#skF_8'))), inference(resolution, [status(thm)], [c_2190, c_4])).
% 3.93/1.68  tff(c_2509, plain, (r1_tarski('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_6, c_2501])).
% 3.93/1.68  tff(c_2515, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2079, c_2079, c_2509])).
% 3.93/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.93/1.68  
% 3.93/1.68  Inference rules
% 3.93/1.68  ----------------------
% 3.93/1.68  #Ref     : 0
% 3.93/1.68  #Sup     : 566
% 3.93/1.68  #Fact    : 0
% 3.93/1.68  #Define  : 0
% 3.93/1.68  #Split   : 6
% 3.93/1.68  #Chain   : 0
% 3.93/1.68  #Close   : 0
% 3.93/1.68  
% 3.93/1.68  Ordering : KBO
% 3.93/1.68  
% 3.93/1.68  Simplification rules
% 3.93/1.68  ----------------------
% 3.93/1.68  #Subsume      : 44
% 3.93/1.68  #Demod        : 348
% 3.93/1.68  #Tautology    : 303
% 3.93/1.68  #SimpNegUnit  : 8
% 3.93/1.68  #BackRed      : 6
% 3.93/1.68  
% 3.93/1.68  #Partial instantiations: 0
% 3.93/1.68  #Strategies tried      : 1
% 3.93/1.68  
% 3.93/1.68  Timing (in seconds)
% 3.93/1.68  ----------------------
% 3.93/1.69  Preprocessing        : 0.33
% 3.93/1.69  Parsing              : 0.16
% 3.93/1.69  CNF conversion       : 0.03
% 3.93/1.69  Main loop            : 0.55
% 3.93/1.69  Inferencing          : 0.20
% 3.93/1.69  Reduction            : 0.19
% 3.93/1.69  Demodulation         : 0.14
% 3.93/1.69  BG Simplification    : 0.03
% 3.93/1.69  Subsumption          : 0.10
% 3.93/1.69  Abstraction          : 0.03
% 3.93/1.69  MUC search           : 0.00
% 3.93/1.69  Cooper               : 0.00
% 3.93/1.69  Total                : 0.91
% 3.93/1.69  Index Insertion      : 0.00
% 3.93/1.69  Index Deletion       : 0.00
% 3.93/1.69  Index Matching       : 0.00
% 3.93/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
