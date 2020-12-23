%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:24 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 147 expanded)
%              Number of leaves         :   24 (  59 expanded)
%              Depth                    :    9
%              Number of atoms          :   97 ( 292 expanded)
%              Number of equality atoms :   39 ( 132 expanded)
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

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & ~ ! [C] :
                ( m1_subset_1(C,k2_zfmisc_1(A,B))
               => ( C != k1_mcart_1(C)
                  & C != k2_mcart_1(C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_mcart_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_60,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ( A != k1_mcart_1(A)
        & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_51,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ~ v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_subset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_20,plain,(
    ! [A_16,B_17] : k2_mcart_1(k4_tarski(A_16,B_17)) = B_17 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_12,plain,(
    ! [B_12,C_13] : k2_mcart_1(k4_tarski(B_12,C_13)) != k4_tarski(B_12,C_13) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_30,plain,(
    ! [B_12,C_13] : k4_tarski(B_12,C_13) != C_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_12])).

tff(c_10,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_18,plain,(
    ! [A_16,B_17] : k1_mcart_1(k4_tarski(A_16,B_17)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_14,plain,(
    ! [B_12,C_13] : k1_mcart_1(k4_tarski(B_12,C_13)) != k4_tarski(B_12,C_13) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_29,plain,(
    ! [B_12,C_13] : k4_tarski(B_12,C_13) != B_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_14])).

tff(c_22,plain,
    ( k2_mcart_1('#skF_3') = '#skF_3'
    | k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_52,plain,(
    k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r2_hidden(A_5,B_6)
      | v1_xboole_0(B_6)
      | ~ m1_subset_1(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_69,plain,(
    ! [A_36,B_37] :
      ( k4_tarski(k1_mcart_1(A_36),k2_mcart_1(A_36)) = A_36
      | ~ r2_hidden(A_36,B_37)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_73,plain,(
    ! [A_38,B_39] :
      ( k4_tarski(k1_mcart_1(A_38),k2_mcart_1(A_38)) = A_38
      | ~ v1_relat_1(B_39)
      | v1_xboole_0(B_39)
      | ~ m1_subset_1(A_38,B_39) ) ),
    inference(resolution,[status(thm)],[c_8,c_69])).

tff(c_75,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2'))
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_73])).

tff(c_78,plain,
    ( k4_tarski('#skF_3',k2_mcart_1('#skF_3')) = '#skF_3'
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_52,c_75])).

tff(c_79,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_29,c_78])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_3,B_4))
      | v1_xboole_0(B_4)
      | v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_88,plain,
    ( v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_79,c_6])).

tff(c_91,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_57,plain,(
    ! [B_29,A_30] :
      ( ~ v1_xboole_0(B_29)
      | B_29 = A_30
      | ~ v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_60,plain,(
    ! [A_30] :
      ( k1_xboole_0 = A_30
      | ~ v1_xboole_0(A_30) ) ),
    inference(resolution,[status(thm)],[c_2,c_57])).

tff(c_108,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_91,c_60])).

tff(c_114,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_108])).

tff(c_115,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_119,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_115,c_60])).

tff(c_125,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_119])).

tff(c_126,plain,(
    k2_mcart_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_144,plain,(
    ! [A_47,B_48] :
      ( k4_tarski(k1_mcart_1(A_47),k2_mcart_1(A_47)) = A_47
      | ~ r2_hidden(A_47,B_48)
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_148,plain,(
    ! [A_49,B_50] :
      ( k4_tarski(k1_mcart_1(A_49),k2_mcart_1(A_49)) = A_49
      | ~ v1_relat_1(B_50)
      | v1_xboole_0(B_50)
      | ~ m1_subset_1(A_49,B_50) ) ),
    inference(resolution,[status(thm)],[c_8,c_144])).

tff(c_150,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2'))
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_148])).

tff(c_153,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),'#skF_3') = '#skF_3'
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_126,c_150])).

tff(c_154,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_153])).

tff(c_163,plain,
    ( v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_154,c_6])).

tff(c_166,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_163])).

tff(c_132,plain,(
    ! [B_40,A_41] :
      ( ~ v1_xboole_0(B_40)
      | B_40 = A_41
      | ~ v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_135,plain,(
    ! [A_41] :
      ( k1_xboole_0 = A_41
      | ~ v1_xboole_0(A_41) ) ),
    inference(resolution,[status(thm)],[c_2,c_132])).

tff(c_169,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_166,c_135])).

tff(c_175,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_169])).

tff(c_176,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_163])).

tff(c_180,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_176,c_135])).

tff(c_186,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_180])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:34:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.27  
% 1.96/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.27  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.96/1.27  
% 1.96/1.27  %Foreground sorts:
% 1.96/1.27  
% 1.96/1.27  
% 1.96/1.27  %Background operators:
% 1.96/1.27  
% 1.96/1.27  
% 1.96/1.27  %Foreground operators:
% 1.96/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.96/1.27  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.96/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.96/1.27  tff('#skF_2', type, '#skF_2': $i).
% 1.96/1.27  tff('#skF_3', type, '#skF_3': $i).
% 1.96/1.27  tff('#skF_1', type, '#skF_1': $i).
% 1.96/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.27  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.96/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.96/1.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.96/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.27  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.96/1.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.96/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.96/1.27  
% 1.96/1.29  tff(f_88, negated_conjecture, ~(![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(![C]: (m1_subset_1(C, k2_zfmisc_1(A, B)) => (~(C = k1_mcart_1(C)) & ~(C = k2_mcart_1(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_mcart_1)).
% 1.96/1.29  tff(f_70, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 1.96/1.29  tff(f_60, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 1.96/1.29  tff(f_51, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.96/1.29  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 1.96/1.29  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_mcart_1)).
% 1.96/1.29  tff(f_43, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => ~v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_subset_1)).
% 1.96/1.29  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.96/1.29  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 1.96/1.29  tff(c_26, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_88])).
% 1.96/1.29  tff(c_28, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_88])).
% 1.96/1.29  tff(c_20, plain, (![A_16, B_17]: (k2_mcart_1(k4_tarski(A_16, B_17))=B_17)), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.96/1.29  tff(c_12, plain, (![B_12, C_13]: (k2_mcart_1(k4_tarski(B_12, C_13))!=k4_tarski(B_12, C_13))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.96/1.29  tff(c_30, plain, (![B_12, C_13]: (k4_tarski(B_12, C_13)!=C_13)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_12])).
% 1.96/1.29  tff(c_10, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.96/1.29  tff(c_18, plain, (![A_16, B_17]: (k1_mcart_1(k4_tarski(A_16, B_17))=A_16)), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.96/1.29  tff(c_14, plain, (![B_12, C_13]: (k1_mcart_1(k4_tarski(B_12, C_13))!=k4_tarski(B_12, C_13))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.96/1.29  tff(c_29, plain, (![B_12, C_13]: (k4_tarski(B_12, C_13)!=B_12)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_14])).
% 1.96/1.29  tff(c_22, plain, (k2_mcart_1('#skF_3')='#skF_3' | k1_mcart_1('#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_88])).
% 1.96/1.29  tff(c_52, plain, (k1_mcart_1('#skF_3')='#skF_3'), inference(splitLeft, [status(thm)], [c_22])).
% 1.96/1.29  tff(c_24, plain, (m1_subset_1('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 1.96/1.29  tff(c_8, plain, (![A_5, B_6]: (r2_hidden(A_5, B_6) | v1_xboole_0(B_6) | ~m1_subset_1(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.96/1.29  tff(c_69, plain, (![A_36, B_37]: (k4_tarski(k1_mcart_1(A_36), k2_mcart_1(A_36))=A_36 | ~r2_hidden(A_36, B_37) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.96/1.29  tff(c_73, plain, (![A_38, B_39]: (k4_tarski(k1_mcart_1(A_38), k2_mcart_1(A_38))=A_38 | ~v1_relat_1(B_39) | v1_xboole_0(B_39) | ~m1_subset_1(A_38, B_39))), inference(resolution, [status(thm)], [c_8, c_69])).
% 1.96/1.29  tff(c_75, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3' | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2')) | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_73])).
% 1.96/1.29  tff(c_78, plain, (k4_tarski('#skF_3', k2_mcart_1('#skF_3'))='#skF_3' | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_52, c_75])).
% 1.96/1.29  tff(c_79, plain, (v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_29, c_78])).
% 1.96/1.29  tff(c_6, plain, (![A_3, B_4]: (~v1_xboole_0(k2_zfmisc_1(A_3, B_4)) | v1_xboole_0(B_4) | v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.96/1.29  tff(c_88, plain, (v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_79, c_6])).
% 1.96/1.29  tff(c_91, plain, (v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_88])).
% 1.96/1.29  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.96/1.29  tff(c_57, plain, (![B_29, A_30]: (~v1_xboole_0(B_29) | B_29=A_30 | ~v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.96/1.29  tff(c_60, plain, (![A_30]: (k1_xboole_0=A_30 | ~v1_xboole_0(A_30))), inference(resolution, [status(thm)], [c_2, c_57])).
% 1.96/1.29  tff(c_108, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_91, c_60])).
% 1.96/1.29  tff(c_114, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_108])).
% 1.96/1.29  tff(c_115, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_88])).
% 1.96/1.29  tff(c_119, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_115, c_60])).
% 1.96/1.29  tff(c_125, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_119])).
% 1.96/1.29  tff(c_126, plain, (k2_mcart_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_22])).
% 1.96/1.29  tff(c_144, plain, (![A_47, B_48]: (k4_tarski(k1_mcart_1(A_47), k2_mcart_1(A_47))=A_47 | ~r2_hidden(A_47, B_48) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.96/1.29  tff(c_148, plain, (![A_49, B_50]: (k4_tarski(k1_mcart_1(A_49), k2_mcart_1(A_49))=A_49 | ~v1_relat_1(B_50) | v1_xboole_0(B_50) | ~m1_subset_1(A_49, B_50))), inference(resolution, [status(thm)], [c_8, c_144])).
% 1.96/1.29  tff(c_150, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3' | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2')) | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_148])).
% 1.96/1.29  tff(c_153, plain, (k4_tarski(k1_mcart_1('#skF_3'), '#skF_3')='#skF_3' | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_126, c_150])).
% 1.96/1.29  tff(c_154, plain, (v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_30, c_153])).
% 1.96/1.29  tff(c_163, plain, (v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_154, c_6])).
% 1.96/1.29  tff(c_166, plain, (v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_163])).
% 1.96/1.29  tff(c_132, plain, (![B_40, A_41]: (~v1_xboole_0(B_40) | B_40=A_41 | ~v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.96/1.29  tff(c_135, plain, (![A_41]: (k1_xboole_0=A_41 | ~v1_xboole_0(A_41))), inference(resolution, [status(thm)], [c_2, c_132])).
% 1.96/1.29  tff(c_169, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_166, c_135])).
% 1.96/1.29  tff(c_175, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_169])).
% 1.96/1.29  tff(c_176, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_163])).
% 1.96/1.29  tff(c_180, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_176, c_135])).
% 1.96/1.29  tff(c_186, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_180])).
% 1.96/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.29  
% 1.96/1.29  Inference rules
% 1.96/1.29  ----------------------
% 1.96/1.29  #Ref     : 0
% 1.96/1.29  #Sup     : 34
% 1.96/1.29  #Fact    : 0
% 1.96/1.29  #Define  : 0
% 1.96/1.29  #Split   : 3
% 1.96/1.29  #Chain   : 0
% 1.96/1.29  #Close   : 0
% 1.96/1.29  
% 1.96/1.29  Ordering : KBO
% 1.96/1.29  
% 1.96/1.29  Simplification rules
% 1.96/1.29  ----------------------
% 1.96/1.29  #Subsume      : 0
% 1.96/1.29  #Demod        : 10
% 1.96/1.29  #Tautology    : 13
% 1.96/1.29  #SimpNegUnit  : 6
% 1.96/1.29  #BackRed      : 2
% 1.96/1.29  
% 1.96/1.29  #Partial instantiations: 0
% 1.96/1.29  #Strategies tried      : 1
% 1.96/1.29  
% 1.96/1.29  Timing (in seconds)
% 1.96/1.29  ----------------------
% 1.96/1.29  Preprocessing        : 0.32
% 1.96/1.29  Parsing              : 0.17
% 1.96/1.29  CNF conversion       : 0.02
% 1.96/1.29  Main loop            : 0.15
% 1.96/1.29  Inferencing          : 0.06
% 1.96/1.29  Reduction            : 0.05
% 1.96/1.29  Demodulation         : 0.03
% 1.96/1.29  BG Simplification    : 0.01
% 1.96/1.29  Subsumption          : 0.02
% 1.96/1.29  Abstraction          : 0.01
% 1.96/1.29  MUC search           : 0.00
% 1.96/1.29  Cooper               : 0.00
% 1.96/1.29  Total                : 0.51
% 1.96/1.29  Index Insertion      : 0.00
% 1.96/1.29  Index Deletion       : 0.00
% 1.96/1.29  Index Matching       : 0.00
% 1.96/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
