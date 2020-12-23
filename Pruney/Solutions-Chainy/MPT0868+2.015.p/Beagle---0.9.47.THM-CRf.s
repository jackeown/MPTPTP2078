%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:25 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   61 (  89 expanded)
%              Number of leaves         :   26 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :   90 ( 172 expanded)
%              Number of equality atoms :   56 ( 116 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_89,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & ~ ! [C] :
                ( m1_subset_1(C,k2_zfmisc_1(A,B))
               => ( C != k1_mcart_1(C)
                  & C != k2_mcart_1(C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_mcart_1)).

tff(f_52,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_61,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ( A != k1_mcart_1(A)
        & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_37,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_67,axiom,(
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

tff(f_49,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_12,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_24,plain,(
    ! [A_15,B_16] : k2_mcart_1(k4_tarski(A_15,B_16)) = B_16 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_16,plain,(
    ! [B_11,C_12] : k2_mcart_1(k4_tarski(B_11,C_12)) != k4_tarski(B_11,C_12) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_34,plain,(
    ! [B_11,C_12] : k4_tarski(B_11,C_12) != C_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_16])).

tff(c_6,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    ! [A_15,B_16] : k1_mcart_1(k4_tarski(A_15,B_16)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_18,plain,(
    ! [B_11,C_12] : k1_mcart_1(k4_tarski(B_11,C_12)) != k4_tarski(B_11,C_12) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_33,plain,(
    ! [B_11,C_12] : k4_tarski(B_11,C_12) != B_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18])).

tff(c_26,plain,
    ( k2_mcart_1('#skF_3') = '#skF_3'
    | k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_65,plain,(
    k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( r2_hidden(A_2,B_3)
      | v1_xboole_0(B_3)
      | ~ m1_subset_1(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_95,plain,(
    ! [A_35,B_36] :
      ( k4_tarski(k1_mcart_1(A_35),k2_mcart_1(A_35)) = A_35
      | ~ r2_hidden(A_35,B_36)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_99,plain,(
    ! [A_37,B_38] :
      ( k4_tarski(k1_mcart_1(A_37),k2_mcart_1(A_37)) = A_37
      | ~ v1_relat_1(B_38)
      | v1_xboole_0(B_38)
      | ~ m1_subset_1(A_37,B_38) ) ),
    inference(resolution,[status(thm)],[c_4,c_95])).

tff(c_101,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2'))
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_28,c_99])).

tff(c_104,plain,
    ( k4_tarski('#skF_3',k2_mcart_1('#skF_3')) = '#skF_3'
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_65,c_101])).

tff(c_105,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_33,c_104])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_109,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_105,c_2])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k2_relat_1(k2_zfmisc_1(A_6,B_7)) = B_7
      | k1_xboole_0 = B_7
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_115,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_8])).

tff(c_123,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_115])).

tff(c_125,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_30,c_123])).

tff(c_126,plain,(
    k2_mcart_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_157,plain,(
    ! [A_45,B_46] :
      ( k4_tarski(k1_mcart_1(A_45),k2_mcart_1(A_45)) = A_45
      | ~ r2_hidden(A_45,B_46)
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_161,plain,(
    ! [A_47,B_48] :
      ( k4_tarski(k1_mcart_1(A_47),k2_mcart_1(A_47)) = A_47
      | ~ v1_relat_1(B_48)
      | v1_xboole_0(B_48)
      | ~ m1_subset_1(A_47,B_48) ) ),
    inference(resolution,[status(thm)],[c_4,c_157])).

tff(c_163,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2'))
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_28,c_161])).

tff(c_166,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),'#skF_3') = '#skF_3'
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_126,c_163])).

tff(c_167,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_166])).

tff(c_171,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_167,c_2])).

tff(c_177,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_8])).

tff(c_185,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_177])).

tff(c_187,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_30,c_185])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:19:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.17  
% 1.63/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.17  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.89/1.17  
% 1.89/1.17  %Foreground sorts:
% 1.89/1.17  
% 1.89/1.17  
% 1.89/1.17  %Background operators:
% 1.89/1.17  
% 1.89/1.17  
% 1.89/1.17  %Foreground operators:
% 1.89/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.89/1.17  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.89/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.89/1.17  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.89/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.89/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.89/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.89/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.17  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.89/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.89/1.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.89/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.17  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.89/1.17  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.89/1.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.89/1.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.89/1.17  
% 1.89/1.18  tff(f_89, negated_conjecture, ~(![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(![C]: (m1_subset_1(C, k2_zfmisc_1(A, B)) => (~(C = k1_mcart_1(C)) & ~(C = k2_mcart_1(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_mcart_1)).
% 1.89/1.18  tff(f_52, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.89/1.18  tff(f_71, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 1.89/1.18  tff(f_61, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 1.89/1.18  tff(f_37, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.89/1.18  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 1.89/1.18  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_mcart_1)).
% 1.89/1.18  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.89/1.18  tff(f_49, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t195_relat_1)).
% 1.89/1.18  tff(c_32, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_89])).
% 1.89/1.18  tff(c_30, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_89])).
% 1.89/1.18  tff(c_12, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.89/1.18  tff(c_24, plain, (![A_15, B_16]: (k2_mcart_1(k4_tarski(A_15, B_16))=B_16)), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.89/1.18  tff(c_16, plain, (![B_11, C_12]: (k2_mcart_1(k4_tarski(B_11, C_12))!=k4_tarski(B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.89/1.18  tff(c_34, plain, (![B_11, C_12]: (k4_tarski(B_11, C_12)!=C_12)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_16])).
% 1.89/1.18  tff(c_6, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.89/1.18  tff(c_22, plain, (![A_15, B_16]: (k1_mcart_1(k4_tarski(A_15, B_16))=A_15)), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.89/1.18  tff(c_18, plain, (![B_11, C_12]: (k1_mcart_1(k4_tarski(B_11, C_12))!=k4_tarski(B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.89/1.18  tff(c_33, plain, (![B_11, C_12]: (k4_tarski(B_11, C_12)!=B_11)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_18])).
% 1.89/1.18  tff(c_26, plain, (k2_mcart_1('#skF_3')='#skF_3' | k1_mcart_1('#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_89])).
% 1.89/1.18  tff(c_65, plain, (k1_mcart_1('#skF_3')='#skF_3'), inference(splitLeft, [status(thm)], [c_26])).
% 1.89/1.18  tff(c_28, plain, (m1_subset_1('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 1.89/1.18  tff(c_4, plain, (![A_2, B_3]: (r2_hidden(A_2, B_3) | v1_xboole_0(B_3) | ~m1_subset_1(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.89/1.18  tff(c_95, plain, (![A_35, B_36]: (k4_tarski(k1_mcart_1(A_35), k2_mcart_1(A_35))=A_35 | ~r2_hidden(A_35, B_36) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.89/1.18  tff(c_99, plain, (![A_37, B_38]: (k4_tarski(k1_mcart_1(A_37), k2_mcart_1(A_37))=A_37 | ~v1_relat_1(B_38) | v1_xboole_0(B_38) | ~m1_subset_1(A_37, B_38))), inference(resolution, [status(thm)], [c_4, c_95])).
% 1.89/1.18  tff(c_101, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3' | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2')) | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_99])).
% 1.89/1.18  tff(c_104, plain, (k4_tarski('#skF_3', k2_mcart_1('#skF_3'))='#skF_3' | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_65, c_101])).
% 1.89/1.18  tff(c_105, plain, (v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_33, c_104])).
% 1.89/1.18  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.89/1.18  tff(c_109, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_105, c_2])).
% 1.89/1.18  tff(c_8, plain, (![A_6, B_7]: (k2_relat_1(k2_zfmisc_1(A_6, B_7))=B_7 | k1_xboole_0=B_7 | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.89/1.18  tff(c_115, plain, (k2_relat_1(k1_xboole_0)='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_109, c_8])).
% 1.89/1.18  tff(c_123, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_115])).
% 1.89/1.18  tff(c_125, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_30, c_123])).
% 1.89/1.18  tff(c_126, plain, (k2_mcart_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_26])).
% 1.89/1.18  tff(c_157, plain, (![A_45, B_46]: (k4_tarski(k1_mcart_1(A_45), k2_mcart_1(A_45))=A_45 | ~r2_hidden(A_45, B_46) | ~v1_relat_1(B_46))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.89/1.18  tff(c_161, plain, (![A_47, B_48]: (k4_tarski(k1_mcart_1(A_47), k2_mcart_1(A_47))=A_47 | ~v1_relat_1(B_48) | v1_xboole_0(B_48) | ~m1_subset_1(A_47, B_48))), inference(resolution, [status(thm)], [c_4, c_157])).
% 1.89/1.18  tff(c_163, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3' | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2')) | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_161])).
% 1.89/1.18  tff(c_166, plain, (k4_tarski(k1_mcart_1('#skF_3'), '#skF_3')='#skF_3' | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_126, c_163])).
% 1.89/1.18  tff(c_167, plain, (v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_34, c_166])).
% 1.89/1.18  tff(c_171, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_167, c_2])).
% 1.89/1.18  tff(c_177, plain, (k2_relat_1(k1_xboole_0)='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_171, c_8])).
% 1.89/1.18  tff(c_185, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_177])).
% 1.89/1.18  tff(c_187, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_30, c_185])).
% 1.89/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.18  
% 1.89/1.18  Inference rules
% 1.89/1.18  ----------------------
% 1.89/1.18  #Ref     : 0
% 1.89/1.18  #Sup     : 36
% 1.89/1.18  #Fact    : 0
% 1.89/1.18  #Define  : 0
% 1.89/1.18  #Split   : 1
% 1.89/1.18  #Chain   : 0
% 1.89/1.18  #Close   : 0
% 1.89/1.18  
% 1.89/1.18  Ordering : KBO
% 1.89/1.18  
% 1.89/1.18  Simplification rules
% 1.89/1.18  ----------------------
% 1.89/1.18  #Subsume      : 0
% 1.89/1.18  #Demod        : 12
% 1.89/1.18  #Tautology    : 22
% 1.89/1.18  #SimpNegUnit  : 4
% 1.89/1.18  #BackRed      : 4
% 1.89/1.18  
% 1.89/1.18  #Partial instantiations: 0
% 1.89/1.18  #Strategies tried      : 1
% 1.89/1.18  
% 1.89/1.18  Timing (in seconds)
% 1.89/1.18  ----------------------
% 1.89/1.19  Preprocessing        : 0.29
% 1.89/1.19  Parsing              : 0.16
% 1.89/1.19  CNF conversion       : 0.02
% 1.89/1.19  Main loop            : 0.14
% 1.89/1.19  Inferencing          : 0.05
% 1.89/1.19  Reduction            : 0.04
% 1.89/1.19  Demodulation         : 0.03
% 1.89/1.19  BG Simplification    : 0.01
% 1.89/1.19  Subsumption          : 0.02
% 1.89/1.19  Abstraction          : 0.01
% 1.89/1.19  MUC search           : 0.00
% 1.89/1.19  Cooper               : 0.00
% 1.89/1.19  Total                : 0.46
% 1.89/1.19  Index Insertion      : 0.00
% 1.89/1.19  Index Deletion       : 0.00
% 1.89/1.19  Index Matching       : 0.00
% 1.89/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
