%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:25 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   55 (  77 expanded)
%              Number of leaves         :   23 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :   78 ( 144 expanded)
%              Number of equality atoms :   44 (  90 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & ~ ! [C] :
                ( m1_subset_1(C,k2_zfmisc_1(A,B))
               => ( C != k1_mcart_1(C)
                  & C != k2_mcart_1(C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_mcart_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_52,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ( A != k1_mcart_1(A)
        & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_43,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_22,plain,(
    ! [A_15,B_16] : k2_mcart_1(k4_tarski(A_15,B_16)) = B_16 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_14,plain,(
    ! [B_11,C_12] : k2_mcart_1(k4_tarski(B_11,C_12)) != k4_tarski(B_11,C_12) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_32,plain,(
    ! [B_11,C_12] : k4_tarski(B_11,C_12) != C_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_14])).

tff(c_12,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [A_15,B_16] : k1_mcart_1(k4_tarski(A_15,B_16)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_16,plain,(
    ! [B_11,C_12] : k1_mcart_1(k4_tarski(B_11,C_12)) != k4_tarski(B_11,C_12) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_31,plain,(
    ! [B_11,C_12] : k4_tarski(B_11,C_12) != B_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_16])).

tff(c_24,plain,
    ( k2_mcart_1('#skF_3') = '#skF_3'
    | k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_82,plain,(
    k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( r2_hidden(A_4,B_5)
      | v1_xboole_0(B_5)
      | ~ m1_subset_1(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_99,plain,(
    ! [A_35,B_36] :
      ( k4_tarski(k1_mcart_1(A_35),k2_mcart_1(A_35)) = A_35
      | ~ r2_hidden(A_35,B_36)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_103,plain,(
    ! [A_37,B_38] :
      ( k4_tarski(k1_mcart_1(A_37),k2_mcart_1(A_37)) = A_37
      | ~ v1_relat_1(B_38)
      | v1_xboole_0(B_38)
      | ~ m1_subset_1(A_37,B_38) ) ),
    inference(resolution,[status(thm)],[c_10,c_99])).

tff(c_105,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2'))
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_26,c_103])).

tff(c_108,plain,
    ( k4_tarski('#skF_3',k2_mcart_1('#skF_3')) = '#skF_3'
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_82,c_105])).

tff(c_109,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_31,c_108])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_113,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_109,c_2])).

tff(c_4,plain,(
    ! [B_3,A_2] :
      ( k1_xboole_0 = B_3
      | k1_xboole_0 = A_2
      | k2_zfmisc_1(A_2,B_3) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_119,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_4])).

tff(c_127,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_119])).

tff(c_128,plain,(
    k2_mcart_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_146,plain,(
    ! [A_43,B_44] :
      ( k4_tarski(k1_mcart_1(A_43),k2_mcart_1(A_43)) = A_43
      | ~ r2_hidden(A_43,B_44)
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_150,plain,(
    ! [A_45,B_46] :
      ( k4_tarski(k1_mcart_1(A_45),k2_mcart_1(A_45)) = A_45
      | ~ v1_relat_1(B_46)
      | v1_xboole_0(B_46)
      | ~ m1_subset_1(A_45,B_46) ) ),
    inference(resolution,[status(thm)],[c_10,c_146])).

tff(c_152,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2'))
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_26,c_150])).

tff(c_155,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),'#skF_3') = '#skF_3'
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_128,c_152])).

tff(c_156,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_155])).

tff(c_160,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_156,c_2])).

tff(c_166,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_4])).

tff(c_174,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_166])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:18:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.26  
% 2.02/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.26  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.02/1.26  
% 2.02/1.26  %Foreground sorts:
% 2.02/1.26  
% 2.02/1.26  
% 2.02/1.26  %Background operators:
% 2.02/1.26  
% 2.02/1.26  
% 2.02/1.26  %Foreground operators:
% 2.02/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.02/1.26  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.02/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.02/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.02/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.02/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.02/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.26  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.02/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.02/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.02/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.26  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.02/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.02/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.02/1.26  
% 2.02/1.27  tff(f_80, negated_conjecture, ~(![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(![C]: (m1_subset_1(C, k2_zfmisc_1(A, B)) => (~(C = k1_mcart_1(C)) & ~(C = k2_mcart_1(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_mcart_1)).
% 2.02/1.27  tff(f_62, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.02/1.27  tff(f_52, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 2.02/1.27  tff(f_43, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.02/1.27  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.02/1.27  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_mcart_1)).
% 2.02/1.27  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.02/1.27  tff(f_35, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.02/1.27  tff(c_30, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.02/1.27  tff(c_28, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.02/1.27  tff(c_22, plain, (![A_15, B_16]: (k2_mcart_1(k4_tarski(A_15, B_16))=B_16)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.02/1.27  tff(c_14, plain, (![B_11, C_12]: (k2_mcart_1(k4_tarski(B_11, C_12))!=k4_tarski(B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.02/1.27  tff(c_32, plain, (![B_11, C_12]: (k4_tarski(B_11, C_12)!=C_12)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_14])).
% 2.02/1.27  tff(c_12, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.02/1.27  tff(c_20, plain, (![A_15, B_16]: (k1_mcart_1(k4_tarski(A_15, B_16))=A_15)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.02/1.27  tff(c_16, plain, (![B_11, C_12]: (k1_mcart_1(k4_tarski(B_11, C_12))!=k4_tarski(B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.02/1.27  tff(c_31, plain, (![B_11, C_12]: (k4_tarski(B_11, C_12)!=B_11)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_16])).
% 2.02/1.27  tff(c_24, plain, (k2_mcart_1('#skF_3')='#skF_3' | k1_mcart_1('#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.02/1.27  tff(c_82, plain, (k1_mcart_1('#skF_3')='#skF_3'), inference(splitLeft, [status(thm)], [c_24])).
% 2.02/1.27  tff(c_26, plain, (m1_subset_1('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.02/1.27  tff(c_10, plain, (![A_4, B_5]: (r2_hidden(A_4, B_5) | v1_xboole_0(B_5) | ~m1_subset_1(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.02/1.27  tff(c_99, plain, (![A_35, B_36]: (k4_tarski(k1_mcart_1(A_35), k2_mcart_1(A_35))=A_35 | ~r2_hidden(A_35, B_36) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.02/1.27  tff(c_103, plain, (![A_37, B_38]: (k4_tarski(k1_mcart_1(A_37), k2_mcart_1(A_37))=A_37 | ~v1_relat_1(B_38) | v1_xboole_0(B_38) | ~m1_subset_1(A_37, B_38))), inference(resolution, [status(thm)], [c_10, c_99])).
% 2.02/1.27  tff(c_105, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3' | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2')) | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_26, c_103])).
% 2.02/1.27  tff(c_108, plain, (k4_tarski('#skF_3', k2_mcart_1('#skF_3'))='#skF_3' | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_82, c_105])).
% 2.02/1.27  tff(c_109, plain, (v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_31, c_108])).
% 2.02/1.27  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.02/1.27  tff(c_113, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_109, c_2])).
% 2.02/1.27  tff(c_4, plain, (![B_3, A_2]: (k1_xboole_0=B_3 | k1_xboole_0=A_2 | k2_zfmisc_1(A_2, B_3)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.02/1.27  tff(c_119, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_113, c_4])).
% 2.02/1.27  tff(c_127, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_28, c_119])).
% 2.02/1.27  tff(c_128, plain, (k2_mcart_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_24])).
% 2.02/1.27  tff(c_146, plain, (![A_43, B_44]: (k4_tarski(k1_mcart_1(A_43), k2_mcart_1(A_43))=A_43 | ~r2_hidden(A_43, B_44) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.02/1.27  tff(c_150, plain, (![A_45, B_46]: (k4_tarski(k1_mcart_1(A_45), k2_mcart_1(A_45))=A_45 | ~v1_relat_1(B_46) | v1_xboole_0(B_46) | ~m1_subset_1(A_45, B_46))), inference(resolution, [status(thm)], [c_10, c_146])).
% 2.02/1.27  tff(c_152, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3' | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2')) | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_26, c_150])).
% 2.02/1.27  tff(c_155, plain, (k4_tarski(k1_mcart_1('#skF_3'), '#skF_3')='#skF_3' | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_128, c_152])).
% 2.02/1.27  tff(c_156, plain, (v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_32, c_155])).
% 2.02/1.27  tff(c_160, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_156, c_2])).
% 2.02/1.27  tff(c_166, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_160, c_4])).
% 2.02/1.27  tff(c_174, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_28, c_166])).
% 2.02/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.27  
% 2.02/1.27  Inference rules
% 2.02/1.27  ----------------------
% 2.02/1.27  #Ref     : 0
% 2.02/1.27  #Sup     : 34
% 2.02/1.27  #Fact    : 0
% 2.02/1.27  #Define  : 0
% 2.02/1.27  #Split   : 1
% 2.02/1.27  #Chain   : 0
% 2.02/1.27  #Close   : 0
% 2.02/1.27  
% 2.02/1.27  Ordering : KBO
% 2.02/1.27  
% 2.02/1.27  Simplification rules
% 2.02/1.27  ----------------------
% 2.02/1.27  #Subsume      : 0
% 2.02/1.27  #Demod        : 11
% 2.02/1.27  #Tautology    : 21
% 2.02/1.27  #SimpNegUnit  : 4
% 2.02/1.27  #BackRed      : 4
% 2.02/1.27  
% 2.02/1.27  #Partial instantiations: 0
% 2.02/1.27  #Strategies tried      : 1
% 2.02/1.27  
% 2.02/1.27  Timing (in seconds)
% 2.02/1.27  ----------------------
% 2.02/1.28  Preprocessing        : 0.32
% 2.02/1.28  Parsing              : 0.17
% 2.02/1.28  CNF conversion       : 0.02
% 2.02/1.28  Main loop            : 0.15
% 2.02/1.28  Inferencing          : 0.05
% 2.02/1.28  Reduction            : 0.05
% 2.02/1.28  Demodulation         : 0.03
% 2.02/1.28  BG Simplification    : 0.01
% 2.02/1.28  Subsumption          : 0.02
% 2.02/1.28  Abstraction          : 0.01
% 2.02/1.28  MUC search           : 0.00
% 2.02/1.28  Cooper               : 0.00
% 2.02/1.28  Total                : 0.50
% 2.02/1.28  Index Insertion      : 0.00
% 2.02/1.28  Index Deletion       : 0.00
% 2.02/1.28  Index Matching       : 0.00
% 2.02/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
