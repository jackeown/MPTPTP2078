%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:41 EST 2020

% Result     : Theorem 3.42s
% Output     : CNFRefutation 3.83s
% Verified   : 
% Statistics : Number of formulae       :   58 (  86 expanded)
%              Number of leaves         :   21 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :   95 ( 171 expanded)
%              Number of equality atoms :    6 (   9 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_xboole_0(B,k3_subset_1(A,C))
            <=> r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

tff(c_22,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_26,plain,
    ( ~ r1_tarski('#skF_3','#skF_4')
    | ~ r1_xboole_0('#skF_3',k3_subset_1('#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_35,plain,(
    ~ r1_xboole_0('#skF_3',k3_subset_1('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_32,plain,
    ( r1_xboole_0('#skF_3',k3_subset_1('#skF_2','#skF_4'))
    | r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_49,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_32])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_20,plain,(
    ! [A_16,C_19,B_17] :
      ( r1_tarski(k3_subset_1(A_16,C_19),k3_subset_1(A_16,B_17))
      | ~ r1_tarski(B_17,C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(A_16))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_111,plain,(
    ! [A_56,B_57] :
      ( k4_xboole_0(A_56,B_57) = k3_subset_1(A_56,B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_119,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k3_subset_1('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_111])).

tff(c_10,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_xboole_0(A_8,C_10)
      | ~ r1_tarski(A_8,k4_xboole_0(B_9,C_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_296,plain,(
    ! [A_72] :
      ( r1_xboole_0(A_72,'#skF_3')
      | ~ r1_tarski(A_72,k3_subset_1('#skF_2','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_10])).

tff(c_300,plain,(
    ! [C_19] :
      ( r1_xboole_0(k3_subset_1('#skF_2',C_19),'#skF_3')
      | ~ r1_tarski('#skF_3',C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_20,c_296])).

tff(c_650,plain,(
    ! [C_153] :
      ( r1_xboole_0(k3_subset_1('#skF_2',C_153),'#skF_3')
      | ~ r1_tarski('#skF_3',C_153)
      | ~ m1_subset_1(C_153,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_300])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( r1_xboole_0(B_7,A_6)
      | ~ r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_675,plain,(
    ! [C_159] :
      ( r1_xboole_0('#skF_3',k3_subset_1('#skF_2',C_159))
      | ~ r1_tarski('#skF_3',C_159)
      | ~ m1_subset_1(C_159,k1_zfmisc_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_650,c_8])).

tff(c_678,plain,
    ( ~ r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_675,c_35])).

tff(c_684,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_49,c_678])).

tff(c_685,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_759,plain,(
    ! [A_187,B_188] :
      ( k4_xboole_0(A_187,B_188) = k3_subset_1(A_187,B_188)
      | ~ m1_subset_1(B_188,k1_zfmisc_1(A_187)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_766,plain,(
    k4_xboole_0('#skF_2','#skF_4') = k3_subset_1('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_759])).

tff(c_694,plain,(
    ! [A_160,B_161] :
      ( r2_hidden('#skF_1'(A_160,B_161),A_160)
      | r1_tarski(A_160,B_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_699,plain,(
    ! [A_160] : r1_tarski(A_160,A_160) ),
    inference(resolution,[status(thm)],[c_694,c_4])).

tff(c_718,plain,(
    ! [A_170,B_171,C_172] :
      ( r1_tarski(A_170,B_171)
      | ~ r1_tarski(A_170,k4_xboole_0(B_171,C_172)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_723,plain,(
    ! [B_171,C_172] : r1_tarski(k4_xboole_0(B_171,C_172),B_171) ),
    inference(resolution,[status(thm)],[c_699,c_718])).

tff(c_780,plain,(
    r1_tarski(k3_subset_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_766,c_723])).

tff(c_686,plain,(
    r1_xboole_0('#skF_3',k3_subset_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_689,plain,(
    r1_xboole_0(k3_subset_1('#skF_2','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_686,c_8])).

tff(c_767,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k3_subset_1('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_759])).

tff(c_14,plain,(
    ! [A_11,B_12,C_13] :
      ( r1_tarski(A_11,k4_xboole_0(B_12,C_13))
      | ~ r1_xboole_0(A_11,C_13)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_999,plain,(
    ! [A_216] :
      ( r1_tarski(A_216,k3_subset_1('#skF_2','#skF_3'))
      | ~ r1_xboole_0(A_216,'#skF_3')
      | ~ r1_tarski(A_216,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_767,c_14])).

tff(c_18,plain,(
    ! [B_17,C_19,A_16] :
      ( r1_tarski(B_17,C_19)
      | ~ r1_tarski(k3_subset_1(A_16,C_19),k3_subset_1(A_16,B_17))
      | ~ m1_subset_1(C_19,k1_zfmisc_1(A_16))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1009,plain,(
    ! [C_19] :
      ( r1_tarski('#skF_3',C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2'))
      | ~ r1_xboole_0(k3_subset_1('#skF_2',C_19),'#skF_3')
      | ~ r1_tarski(k3_subset_1('#skF_2',C_19),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_999,c_18])).

tff(c_1370,plain,(
    ! [C_305] :
      ( r1_tarski('#skF_3',C_305)
      | ~ m1_subset_1(C_305,k1_zfmisc_1('#skF_2'))
      | ~ r1_xboole_0(k3_subset_1('#skF_2',C_305),'#skF_3')
      | ~ r1_tarski(k3_subset_1('#skF_2',C_305),'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1009])).

tff(c_1379,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | ~ r1_tarski(k3_subset_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_689,c_1370])).

tff(c_1386,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_780,c_22,c_1379])).

tff(c_1388,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_685,c_1386])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:09:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.42/1.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.42/1.63  
% 3.42/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.42/1.63  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.42/1.63  
% 3.42/1.63  %Foreground sorts:
% 3.42/1.63  
% 3.42/1.63  
% 3.42/1.63  %Background operators:
% 3.42/1.63  
% 3.42/1.63  
% 3.42/1.63  %Foreground operators:
% 3.42/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.42/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.42/1.63  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.42/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.42/1.63  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.42/1.63  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.42/1.63  tff('#skF_2', type, '#skF_2': $i).
% 3.42/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.42/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.42/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.42/1.63  tff('#skF_4', type, '#skF_4': $i).
% 3.42/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.42/1.63  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.42/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.42/1.63  
% 3.83/1.64  tff(f_71, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, k3_subset_1(A, C)) <=> r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_subset_1)).
% 3.83/1.64  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 3.83/1.64  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.83/1.64  tff(f_42, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 3.83/1.64  tff(f_36, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.83/1.64  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.83/1.64  tff(f_48, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 3.83/1.64  tff(c_22, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.83/1.64  tff(c_26, plain, (~r1_tarski('#skF_3', '#skF_4') | ~r1_xboole_0('#skF_3', k3_subset_1('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.83/1.64  tff(c_35, plain, (~r1_xboole_0('#skF_3', k3_subset_1('#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_26])).
% 3.83/1.64  tff(c_32, plain, (r1_xboole_0('#skF_3', k3_subset_1('#skF_2', '#skF_4')) | r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.83/1.64  tff(c_49, plain, (r1_tarski('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_35, c_32])).
% 3.83/1.64  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.83/1.64  tff(c_20, plain, (![A_16, C_19, B_17]: (r1_tarski(k3_subset_1(A_16, C_19), k3_subset_1(A_16, B_17)) | ~r1_tarski(B_17, C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(A_16)) | ~m1_subset_1(B_17, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.83/1.64  tff(c_111, plain, (![A_56, B_57]: (k4_xboole_0(A_56, B_57)=k3_subset_1(A_56, B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.83/1.64  tff(c_119, plain, (k4_xboole_0('#skF_2', '#skF_3')=k3_subset_1('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_24, c_111])).
% 3.83/1.64  tff(c_10, plain, (![A_8, C_10, B_9]: (r1_xboole_0(A_8, C_10) | ~r1_tarski(A_8, k4_xboole_0(B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.83/1.64  tff(c_296, plain, (![A_72]: (r1_xboole_0(A_72, '#skF_3') | ~r1_tarski(A_72, k3_subset_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_119, c_10])).
% 3.83/1.64  tff(c_300, plain, (![C_19]: (r1_xboole_0(k3_subset_1('#skF_2', C_19), '#skF_3') | ~r1_tarski('#skF_3', C_19) | ~m1_subset_1(C_19, k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_20, c_296])).
% 3.83/1.64  tff(c_650, plain, (![C_153]: (r1_xboole_0(k3_subset_1('#skF_2', C_153), '#skF_3') | ~r1_tarski('#skF_3', C_153) | ~m1_subset_1(C_153, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_300])).
% 3.83/1.64  tff(c_8, plain, (![B_7, A_6]: (r1_xboole_0(B_7, A_6) | ~r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.83/1.64  tff(c_675, plain, (![C_159]: (r1_xboole_0('#skF_3', k3_subset_1('#skF_2', C_159)) | ~r1_tarski('#skF_3', C_159) | ~m1_subset_1(C_159, k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_650, c_8])).
% 3.83/1.64  tff(c_678, plain, (~r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_675, c_35])).
% 3.83/1.64  tff(c_684, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_49, c_678])).
% 3.83/1.64  tff(c_685, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_26])).
% 3.83/1.64  tff(c_759, plain, (![A_187, B_188]: (k4_xboole_0(A_187, B_188)=k3_subset_1(A_187, B_188) | ~m1_subset_1(B_188, k1_zfmisc_1(A_187)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.83/1.64  tff(c_766, plain, (k4_xboole_0('#skF_2', '#skF_4')=k3_subset_1('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_22, c_759])).
% 3.83/1.64  tff(c_694, plain, (![A_160, B_161]: (r2_hidden('#skF_1'(A_160, B_161), A_160) | r1_tarski(A_160, B_161))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.83/1.64  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.83/1.64  tff(c_699, plain, (![A_160]: (r1_tarski(A_160, A_160))), inference(resolution, [status(thm)], [c_694, c_4])).
% 3.83/1.64  tff(c_718, plain, (![A_170, B_171, C_172]: (r1_tarski(A_170, B_171) | ~r1_tarski(A_170, k4_xboole_0(B_171, C_172)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.83/1.64  tff(c_723, plain, (![B_171, C_172]: (r1_tarski(k4_xboole_0(B_171, C_172), B_171))), inference(resolution, [status(thm)], [c_699, c_718])).
% 3.83/1.64  tff(c_780, plain, (r1_tarski(k3_subset_1('#skF_2', '#skF_4'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_766, c_723])).
% 3.83/1.64  tff(c_686, plain, (r1_xboole_0('#skF_3', k3_subset_1('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_26])).
% 3.83/1.64  tff(c_689, plain, (r1_xboole_0(k3_subset_1('#skF_2', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_686, c_8])).
% 3.83/1.64  tff(c_767, plain, (k4_xboole_0('#skF_2', '#skF_3')=k3_subset_1('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_24, c_759])).
% 3.83/1.64  tff(c_14, plain, (![A_11, B_12, C_13]: (r1_tarski(A_11, k4_xboole_0(B_12, C_13)) | ~r1_xboole_0(A_11, C_13) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.83/1.64  tff(c_999, plain, (![A_216]: (r1_tarski(A_216, k3_subset_1('#skF_2', '#skF_3')) | ~r1_xboole_0(A_216, '#skF_3') | ~r1_tarski(A_216, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_767, c_14])).
% 3.83/1.64  tff(c_18, plain, (![B_17, C_19, A_16]: (r1_tarski(B_17, C_19) | ~r1_tarski(k3_subset_1(A_16, C_19), k3_subset_1(A_16, B_17)) | ~m1_subset_1(C_19, k1_zfmisc_1(A_16)) | ~m1_subset_1(B_17, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.83/1.64  tff(c_1009, plain, (![C_19]: (r1_tarski('#skF_3', C_19) | ~m1_subset_1(C_19, k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2')) | ~r1_xboole_0(k3_subset_1('#skF_2', C_19), '#skF_3') | ~r1_tarski(k3_subset_1('#skF_2', C_19), '#skF_2'))), inference(resolution, [status(thm)], [c_999, c_18])).
% 3.83/1.64  tff(c_1370, plain, (![C_305]: (r1_tarski('#skF_3', C_305) | ~m1_subset_1(C_305, k1_zfmisc_1('#skF_2')) | ~r1_xboole_0(k3_subset_1('#skF_2', C_305), '#skF_3') | ~r1_tarski(k3_subset_1('#skF_2', C_305), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1009])).
% 3.83/1.64  tff(c_1379, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | ~r1_tarski(k3_subset_1('#skF_2', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_689, c_1370])).
% 3.83/1.64  tff(c_1386, plain, (r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_780, c_22, c_1379])).
% 3.83/1.64  tff(c_1388, plain, $false, inference(negUnitSimplification, [status(thm)], [c_685, c_1386])).
% 3.83/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.83/1.64  
% 3.83/1.64  Inference rules
% 3.83/1.64  ----------------------
% 3.83/1.64  #Ref     : 0
% 3.83/1.64  #Sup     : 305
% 3.83/1.64  #Fact    : 0
% 3.83/1.64  #Define  : 0
% 3.83/1.64  #Split   : 1
% 3.83/1.64  #Chain   : 0
% 3.83/1.64  #Close   : 0
% 3.83/1.64  
% 3.83/1.64  Ordering : KBO
% 3.83/1.64  
% 3.83/1.64  Simplification rules
% 3.83/1.64  ----------------------
% 3.83/1.64  #Subsume      : 11
% 3.83/1.64  #Demod        : 101
% 3.83/1.64  #Tautology    : 108
% 3.83/1.64  #SimpNegUnit  : 3
% 3.83/1.64  #BackRed      : 0
% 3.83/1.64  
% 3.83/1.64  #Partial instantiations: 0
% 3.83/1.64  #Strategies tried      : 1
% 3.83/1.64  
% 3.83/1.64  Timing (in seconds)
% 3.83/1.64  ----------------------
% 3.83/1.65  Preprocessing        : 0.30
% 3.83/1.65  Parsing              : 0.16
% 3.83/1.65  CNF conversion       : 0.02
% 3.83/1.65  Main loop            : 0.56
% 3.83/1.65  Inferencing          : 0.22
% 3.83/1.65  Reduction            : 0.18
% 3.83/1.65  Demodulation         : 0.13
% 3.83/1.65  BG Simplification    : 0.02
% 3.83/1.65  Subsumption          : 0.11
% 3.83/1.65  Abstraction          : 0.02
% 3.83/1.65  MUC search           : 0.00
% 3.83/1.65  Cooper               : 0.00
% 3.83/1.65  Total                : 0.89
% 3.83/1.65  Index Insertion      : 0.00
% 3.83/1.65  Index Deletion       : 0.00
% 3.83/1.65  Index Matching       : 0.00
% 3.83/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
