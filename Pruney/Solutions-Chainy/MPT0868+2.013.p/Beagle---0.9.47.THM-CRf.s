%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:25 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   60 (  83 expanded)
%              Number of leaves         :   24 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :   89 ( 156 expanded)
%              Number of equality atoms :   47 (  92 expanded)
%              Maximal formula depth    :   12 (   4 average)
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

tff(f_85,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & ~ ! [C] :
                ( m1_subset_1(C,k2_zfmisc_1(A,B))
               => ( C != k1_mcart_1(C)
                  & C != k2_mcart_1(C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_mcart_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_57,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ( A != k1_mcart_1(A)
        & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_48,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_24,plain,(
    ! [A_16,B_17] : k2_mcart_1(k4_tarski(A_16,B_17)) = B_17 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_16,plain,(
    ! [B_12,C_13] : k2_mcart_1(k4_tarski(B_12,C_13)) != k4_tarski(B_12,C_13) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_34,plain,(
    ! [B_12,C_13] : k4_tarski(B_12,C_13) != C_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_16])).

tff(c_14,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_22,plain,(
    ! [A_16,B_17] : k1_mcart_1(k4_tarski(A_16,B_17)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_18,plain,(
    ! [B_12,C_13] : k1_mcart_1(k4_tarski(B_12,C_13)) != k4_tarski(B_12,C_13) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_33,plain,(
    ! [B_12,C_13] : k4_tarski(B_12,C_13) != B_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18])).

tff(c_26,plain,
    ( k2_mcart_1('#skF_3') = '#skF_3'
    | k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_83,plain,(
    k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r2_hidden(A_5,B_6)
      | v1_xboole_0(B_6)
      | ~ m1_subset_1(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_110,plain,(
    ! [A_38,B_39] :
      ( k4_tarski(k1_mcart_1(A_38),k2_mcart_1(A_38)) = A_38
      | ~ r2_hidden(A_38,B_39)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_114,plain,(
    ! [A_40,B_41] :
      ( k4_tarski(k1_mcart_1(A_40),k2_mcart_1(A_40)) = A_40
      | ~ v1_relat_1(B_41)
      | v1_xboole_0(B_41)
      | ~ m1_subset_1(A_40,B_41) ) ),
    inference(resolution,[status(thm)],[c_12,c_110])).

tff(c_116,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2'))
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_28,c_114])).

tff(c_119,plain,
    ( k4_tarski('#skF_3',k2_mcart_1('#skF_3')) = '#skF_3'
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_83,c_116])).

tff(c_120,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_33,c_119])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_88,plain,(
    ! [B_31,A_32] :
      ( ~ v1_xboole_0(B_31)
      | B_31 = A_32
      | ~ v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_91,plain,(
    ! [A_32] :
      ( k1_xboole_0 = A_32
      | ~ v1_xboole_0(A_32) ) ),
    inference(resolution,[status(thm)],[c_2,c_88])).

tff(c_126,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_120,c_91])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_134,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_6])).

tff(c_142,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_134])).

tff(c_143,plain,(
    k2_mcart_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_171,plain,(
    ! [A_49,B_50] :
      ( k4_tarski(k1_mcart_1(A_49),k2_mcart_1(A_49)) = A_49
      | ~ r2_hidden(A_49,B_50)
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_175,plain,(
    ! [A_51,B_52] :
      ( k4_tarski(k1_mcart_1(A_51),k2_mcart_1(A_51)) = A_51
      | ~ v1_relat_1(B_52)
      | v1_xboole_0(B_52)
      | ~ m1_subset_1(A_51,B_52) ) ),
    inference(resolution,[status(thm)],[c_12,c_171])).

tff(c_177,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2'))
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_28,c_175])).

tff(c_180,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),'#skF_3') = '#skF_3'
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_143,c_177])).

tff(c_181,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_180])).

tff(c_149,plain,(
    ! [B_42,A_43] :
      ( ~ v1_xboole_0(B_42)
      | B_42 = A_43
      | ~ v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_152,plain,(
    ! [A_43] :
      ( k1_xboole_0 = A_43
      | ~ v1_xboole_0(A_43) ) ),
    inference(resolution,[status(thm)],[c_2,c_149])).

tff(c_187,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_181,c_152])).

tff(c_195,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_6])).

tff(c_203,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_195])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:35:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.70/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.15  
% 1.70/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.15  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.70/1.15  
% 1.70/1.15  %Foreground sorts:
% 1.70/1.15  
% 1.70/1.15  
% 1.70/1.15  %Background operators:
% 1.70/1.15  
% 1.70/1.15  
% 1.70/1.15  %Foreground operators:
% 1.70/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.70/1.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.70/1.15  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.70/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.70/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.70/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.70/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.70/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.70/1.15  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.70/1.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.70/1.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.70/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.70/1.15  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.70/1.15  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.70/1.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.70/1.15  
% 1.70/1.16  tff(f_85, negated_conjecture, ~(![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(![C]: (m1_subset_1(C, k2_zfmisc_1(A, B)) => (~(C = k1_mcart_1(C)) & ~(C = k2_mcart_1(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_mcart_1)).
% 1.70/1.16  tff(f_67, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 1.70/1.16  tff(f_57, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 1.70/1.16  tff(f_48, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.70/1.16  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 1.70/1.16  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_mcart_1)).
% 1.70/1.16  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.70/1.16  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 1.70/1.16  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.70/1.16  tff(c_32, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_85])).
% 1.70/1.16  tff(c_30, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_85])).
% 1.70/1.16  tff(c_24, plain, (![A_16, B_17]: (k2_mcart_1(k4_tarski(A_16, B_17))=B_17)), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.70/1.16  tff(c_16, plain, (![B_12, C_13]: (k2_mcart_1(k4_tarski(B_12, C_13))!=k4_tarski(B_12, C_13))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.70/1.16  tff(c_34, plain, (![B_12, C_13]: (k4_tarski(B_12, C_13)!=C_13)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_16])).
% 1.70/1.16  tff(c_14, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.70/1.16  tff(c_22, plain, (![A_16, B_17]: (k1_mcart_1(k4_tarski(A_16, B_17))=A_16)), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.70/1.16  tff(c_18, plain, (![B_12, C_13]: (k1_mcart_1(k4_tarski(B_12, C_13))!=k4_tarski(B_12, C_13))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.70/1.16  tff(c_33, plain, (![B_12, C_13]: (k4_tarski(B_12, C_13)!=B_12)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_18])).
% 1.70/1.16  tff(c_26, plain, (k2_mcart_1('#skF_3')='#skF_3' | k1_mcart_1('#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_85])).
% 1.70/1.16  tff(c_83, plain, (k1_mcart_1('#skF_3')='#skF_3'), inference(splitLeft, [status(thm)], [c_26])).
% 1.70/1.16  tff(c_28, plain, (m1_subset_1('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 1.70/1.16  tff(c_12, plain, (![A_5, B_6]: (r2_hidden(A_5, B_6) | v1_xboole_0(B_6) | ~m1_subset_1(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.70/1.16  tff(c_110, plain, (![A_38, B_39]: (k4_tarski(k1_mcart_1(A_38), k2_mcart_1(A_38))=A_38 | ~r2_hidden(A_38, B_39) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.70/1.16  tff(c_114, plain, (![A_40, B_41]: (k4_tarski(k1_mcart_1(A_40), k2_mcart_1(A_40))=A_40 | ~v1_relat_1(B_41) | v1_xboole_0(B_41) | ~m1_subset_1(A_40, B_41))), inference(resolution, [status(thm)], [c_12, c_110])).
% 1.70/1.16  tff(c_116, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3' | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2')) | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_114])).
% 1.70/1.16  tff(c_119, plain, (k4_tarski('#skF_3', k2_mcart_1('#skF_3'))='#skF_3' | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_83, c_116])).
% 1.70/1.16  tff(c_120, plain, (v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_33, c_119])).
% 1.70/1.16  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.70/1.16  tff(c_88, plain, (![B_31, A_32]: (~v1_xboole_0(B_31) | B_31=A_32 | ~v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.70/1.16  tff(c_91, plain, (![A_32]: (k1_xboole_0=A_32 | ~v1_xboole_0(A_32))), inference(resolution, [status(thm)], [c_2, c_88])).
% 1.70/1.16  tff(c_126, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_120, c_91])).
% 1.70/1.16  tff(c_6, plain, (![B_4, A_3]: (k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.70/1.16  tff(c_134, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_126, c_6])).
% 1.70/1.16  tff(c_142, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_134])).
% 1.70/1.16  tff(c_143, plain, (k2_mcart_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_26])).
% 1.70/1.16  tff(c_171, plain, (![A_49, B_50]: (k4_tarski(k1_mcart_1(A_49), k2_mcart_1(A_49))=A_49 | ~r2_hidden(A_49, B_50) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.70/1.16  tff(c_175, plain, (![A_51, B_52]: (k4_tarski(k1_mcart_1(A_51), k2_mcart_1(A_51))=A_51 | ~v1_relat_1(B_52) | v1_xboole_0(B_52) | ~m1_subset_1(A_51, B_52))), inference(resolution, [status(thm)], [c_12, c_171])).
% 1.70/1.16  tff(c_177, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3' | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2')) | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_175])).
% 1.70/1.16  tff(c_180, plain, (k4_tarski(k1_mcart_1('#skF_3'), '#skF_3')='#skF_3' | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_143, c_177])).
% 1.70/1.16  tff(c_181, plain, (v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_34, c_180])).
% 1.70/1.16  tff(c_149, plain, (![B_42, A_43]: (~v1_xboole_0(B_42) | B_42=A_43 | ~v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.70/1.16  tff(c_152, plain, (![A_43]: (k1_xboole_0=A_43 | ~v1_xboole_0(A_43))), inference(resolution, [status(thm)], [c_2, c_149])).
% 1.70/1.16  tff(c_187, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_181, c_152])).
% 1.70/1.16  tff(c_195, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_187, c_6])).
% 1.70/1.16  tff(c_203, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_195])).
% 1.70/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.16  
% 1.70/1.16  Inference rules
% 1.70/1.16  ----------------------
% 1.70/1.16  #Ref     : 0
% 1.70/1.16  #Sup     : 40
% 1.70/1.16  #Fact    : 0
% 1.70/1.16  #Define  : 0
% 1.70/1.16  #Split   : 1
% 1.70/1.16  #Chain   : 0
% 1.70/1.16  #Close   : 0
% 1.70/1.16  
% 1.70/1.16  Ordering : KBO
% 1.70/1.16  
% 1.70/1.16  Simplification rules
% 1.70/1.16  ----------------------
% 1.70/1.16  #Subsume      : 0
% 1.70/1.16  #Demod        : 13
% 1.70/1.16  #Tautology    : 25
% 1.70/1.16  #SimpNegUnit  : 4
% 1.70/1.16  #BackRed      : 4
% 1.70/1.16  
% 1.70/1.16  #Partial instantiations: 0
% 1.70/1.16  #Strategies tried      : 1
% 1.70/1.16  
% 1.70/1.16  Timing (in seconds)
% 1.70/1.16  ----------------------
% 1.70/1.17  Preprocessing        : 0.28
% 1.70/1.17  Parsing              : 0.15
% 1.70/1.17  CNF conversion       : 0.02
% 1.70/1.17  Main loop            : 0.14
% 1.70/1.17  Inferencing          : 0.05
% 1.70/1.17  Reduction            : 0.05
% 1.70/1.17  Demodulation         : 0.03
% 1.70/1.17  BG Simplification    : 0.01
% 1.70/1.17  Subsumption          : 0.02
% 1.70/1.17  Abstraction          : 0.01
% 1.70/1.17  MUC search           : 0.00
% 1.70/1.17  Cooper               : 0.00
% 1.70/1.17  Total                : 0.46
% 1.70/1.17  Index Insertion      : 0.00
% 1.70/1.17  Index Deletion       : 0.00
% 1.70/1.17  Index Matching       : 0.00
% 1.70/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
