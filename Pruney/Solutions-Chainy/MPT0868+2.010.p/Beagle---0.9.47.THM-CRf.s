%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:24 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 135 expanded)
%              Number of leaves         :   23 (  55 expanded)
%              Depth                    :    9
%              Number of atoms          :   86 ( 268 expanded)
%              Number of equality atoms :   36 ( 128 expanded)
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

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & ~ ! [C] :
                ( m1_subset_1(C,k2_zfmisc_1(A,B))
               => ( C != k1_mcart_1(C)
                  & C != k2_mcart_1(C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_mcart_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_55,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ( A != k1_mcart_1(A)
        & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ~ v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_subset_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_18,plain,(
    ! [A_15,B_16] : k2_mcart_1(k4_tarski(A_15,B_16)) = B_16 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_10,plain,(
    ! [B_11,C_12] : k2_mcart_1(k4_tarski(B_11,C_12)) != k4_tarski(B_11,C_12) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_28,plain,(
    ! [B_11,C_12] : k4_tarski(B_11,C_12) != C_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_10])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_16,plain,(
    ! [A_15,B_16] : k1_mcart_1(k4_tarski(A_15,B_16)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_12,plain,(
    ! [B_11,C_12] : k1_mcart_1(k4_tarski(B_11,C_12)) != k4_tarski(B_11,C_12) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_27,plain,(
    ! [B_11,C_12] : k4_tarski(B_11,C_12) != B_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_12])).

tff(c_20,plain,
    ( k2_mcart_1('#skF_3') = '#skF_3'
    | k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_51,plain,(
    k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( r2_hidden(A_4,B_5)
      | v1_xboole_0(B_5)
      | ~ m1_subset_1(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_58,plain,(
    ! [A_33,B_34] :
      ( k4_tarski(k1_mcart_1(A_33),k2_mcart_1(A_33)) = A_33
      | ~ r2_hidden(A_33,B_34)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_62,plain,(
    ! [A_35,B_36] :
      ( k4_tarski(k1_mcart_1(A_35),k2_mcart_1(A_35)) = A_35
      | ~ v1_relat_1(B_36)
      | v1_xboole_0(B_36)
      | ~ m1_subset_1(A_35,B_36) ) ),
    inference(resolution,[status(thm)],[c_6,c_58])).

tff(c_64,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2'))
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_22,c_62])).

tff(c_67,plain,
    ( k4_tarski('#skF_3',k2_mcart_1('#skF_3')) = '#skF_3'
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_51,c_64])).

tff(c_68,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_27,c_67])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_2,B_3))
      | v1_xboole_0(B_3)
      | v1_xboole_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_75,plain,
    ( v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_4])).

tff(c_77,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_75])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_80,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_77,c_2])).

tff(c_84,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_80])).

tff(c_85,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_101,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_85,c_2])).

tff(c_105,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_101])).

tff(c_106,plain,(
    k2_mcart_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_114,plain,(
    ! [A_41,B_42] :
      ( k4_tarski(k1_mcart_1(A_41),k2_mcart_1(A_41)) = A_41
      | ~ r2_hidden(A_41,B_42)
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_118,plain,(
    ! [A_43,B_44] :
      ( k4_tarski(k1_mcart_1(A_43),k2_mcart_1(A_43)) = A_43
      | ~ v1_relat_1(B_44)
      | v1_xboole_0(B_44)
      | ~ m1_subset_1(A_43,B_44) ) ),
    inference(resolution,[status(thm)],[c_6,c_114])).

tff(c_120,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2'))
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_22,c_118])).

tff(c_123,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),'#skF_3') = '#skF_3'
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_106,c_120])).

tff(c_124,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_123])).

tff(c_131,plain,
    ( v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_124,c_4])).

tff(c_133,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_131])).

tff(c_152,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_133,c_2])).

tff(c_156,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_152])).

tff(c_157,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_131])).

tff(c_161,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_157,c_2])).

tff(c_165,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_161])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:45:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.23  
% 1.93/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.24  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.93/1.24  
% 1.93/1.24  %Foreground sorts:
% 1.93/1.24  
% 1.93/1.24  
% 1.93/1.24  %Background operators:
% 1.93/1.24  
% 1.93/1.24  
% 1.93/1.24  %Foreground operators:
% 1.93/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.93/1.24  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.93/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.93/1.24  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.24  tff('#skF_3', type, '#skF_3': $i).
% 1.93/1.24  tff('#skF_1', type, '#skF_1': $i).
% 1.93/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.24  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.93/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.93/1.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.93/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.24  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.93/1.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.93/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.93/1.24  
% 1.93/1.25  tff(f_83, negated_conjecture, ~(![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(![C]: (m1_subset_1(C, k2_zfmisc_1(A, B)) => (~(C = k1_mcart_1(C)) & ~(C = k2_mcart_1(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_mcart_1)).
% 1.93/1.25  tff(f_65, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 1.93/1.25  tff(f_55, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 1.93/1.25  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.93/1.25  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 1.93/1.25  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_mcart_1)).
% 1.93/1.25  tff(f_38, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => ~v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_subset_1)).
% 1.93/1.25  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.93/1.25  tff(c_24, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_83])).
% 1.93/1.25  tff(c_26, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_83])).
% 1.93/1.25  tff(c_18, plain, (![A_15, B_16]: (k2_mcart_1(k4_tarski(A_15, B_16))=B_16)), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.93/1.25  tff(c_10, plain, (![B_11, C_12]: (k2_mcart_1(k4_tarski(B_11, C_12))!=k4_tarski(B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.93/1.25  tff(c_28, plain, (![B_11, C_12]: (k4_tarski(B_11, C_12)!=C_12)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_10])).
% 1.93/1.25  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.93/1.25  tff(c_16, plain, (![A_15, B_16]: (k1_mcart_1(k4_tarski(A_15, B_16))=A_15)), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.93/1.25  tff(c_12, plain, (![B_11, C_12]: (k1_mcart_1(k4_tarski(B_11, C_12))!=k4_tarski(B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.93/1.25  tff(c_27, plain, (![B_11, C_12]: (k4_tarski(B_11, C_12)!=B_11)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_12])).
% 1.93/1.25  tff(c_20, plain, (k2_mcart_1('#skF_3')='#skF_3' | k1_mcart_1('#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_83])).
% 1.93/1.25  tff(c_51, plain, (k1_mcart_1('#skF_3')='#skF_3'), inference(splitLeft, [status(thm)], [c_20])).
% 1.93/1.25  tff(c_22, plain, (m1_subset_1('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 1.93/1.25  tff(c_6, plain, (![A_4, B_5]: (r2_hidden(A_4, B_5) | v1_xboole_0(B_5) | ~m1_subset_1(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.93/1.25  tff(c_58, plain, (![A_33, B_34]: (k4_tarski(k1_mcart_1(A_33), k2_mcart_1(A_33))=A_33 | ~r2_hidden(A_33, B_34) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.93/1.25  tff(c_62, plain, (![A_35, B_36]: (k4_tarski(k1_mcart_1(A_35), k2_mcart_1(A_35))=A_35 | ~v1_relat_1(B_36) | v1_xboole_0(B_36) | ~m1_subset_1(A_35, B_36))), inference(resolution, [status(thm)], [c_6, c_58])).
% 1.93/1.25  tff(c_64, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3' | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2')) | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_22, c_62])).
% 1.93/1.25  tff(c_67, plain, (k4_tarski('#skF_3', k2_mcart_1('#skF_3'))='#skF_3' | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_51, c_64])).
% 1.93/1.25  tff(c_68, plain, (v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_27, c_67])).
% 1.93/1.25  tff(c_4, plain, (![A_2, B_3]: (~v1_xboole_0(k2_zfmisc_1(A_2, B_3)) | v1_xboole_0(B_3) | v1_xboole_0(A_2))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.93/1.25  tff(c_75, plain, (v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_68, c_4])).
% 1.93/1.25  tff(c_77, plain, (v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_75])).
% 1.93/1.25  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.93/1.25  tff(c_80, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_77, c_2])).
% 1.93/1.25  tff(c_84, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_80])).
% 1.93/1.25  tff(c_85, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_75])).
% 1.93/1.25  tff(c_101, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_85, c_2])).
% 1.93/1.25  tff(c_105, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_101])).
% 1.93/1.25  tff(c_106, plain, (k2_mcart_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_20])).
% 1.93/1.25  tff(c_114, plain, (![A_41, B_42]: (k4_tarski(k1_mcart_1(A_41), k2_mcart_1(A_41))=A_41 | ~r2_hidden(A_41, B_42) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.93/1.25  tff(c_118, plain, (![A_43, B_44]: (k4_tarski(k1_mcart_1(A_43), k2_mcart_1(A_43))=A_43 | ~v1_relat_1(B_44) | v1_xboole_0(B_44) | ~m1_subset_1(A_43, B_44))), inference(resolution, [status(thm)], [c_6, c_114])).
% 1.93/1.25  tff(c_120, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3' | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2')) | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_22, c_118])).
% 1.93/1.25  tff(c_123, plain, (k4_tarski(k1_mcart_1('#skF_3'), '#skF_3')='#skF_3' | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_106, c_120])).
% 1.93/1.25  tff(c_124, plain, (v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_28, c_123])).
% 1.93/1.25  tff(c_131, plain, (v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_124, c_4])).
% 1.93/1.25  tff(c_133, plain, (v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_131])).
% 1.93/1.25  tff(c_152, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_133, c_2])).
% 1.93/1.25  tff(c_156, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_152])).
% 1.93/1.25  tff(c_157, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_131])).
% 1.93/1.25  tff(c_161, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_157, c_2])).
% 1.93/1.25  tff(c_165, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_161])).
% 1.93/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.25  
% 1.93/1.25  Inference rules
% 1.93/1.25  ----------------------
% 1.93/1.25  #Ref     : 0
% 1.93/1.25  #Sup     : 29
% 1.93/1.25  #Fact    : 0
% 1.93/1.25  #Define  : 0
% 1.93/1.25  #Split   : 3
% 1.93/1.25  #Chain   : 0
% 1.93/1.25  #Close   : 0
% 1.93/1.25  
% 1.93/1.25  Ordering : KBO
% 1.93/1.25  
% 1.93/1.25  Simplification rules
% 1.93/1.25  ----------------------
% 1.93/1.25  #Subsume      : 0
% 1.93/1.25  #Demod        : 10
% 1.93/1.25  #Tautology    : 13
% 1.93/1.25  #SimpNegUnit  : 7
% 1.93/1.25  #BackRed      : 4
% 1.93/1.25  
% 1.93/1.25  #Partial instantiations: 0
% 1.93/1.25  #Strategies tried      : 1
% 1.93/1.25  
% 1.93/1.25  Timing (in seconds)
% 1.93/1.25  ----------------------
% 2.07/1.25  Preprocessing        : 0.28
% 2.07/1.25  Parsing              : 0.15
% 2.07/1.25  CNF conversion       : 0.02
% 2.07/1.25  Main loop            : 0.14
% 2.07/1.25  Inferencing          : 0.05
% 2.07/1.25  Reduction            : 0.05
% 2.07/1.26  Demodulation         : 0.03
% 2.07/1.26  BG Simplification    : 0.01
% 2.07/1.26  Subsumption          : 0.02
% 2.07/1.26  Abstraction          : 0.01
% 2.07/1.26  MUC search           : 0.00
% 2.07/1.26  Cooper               : 0.00
% 2.07/1.26  Total                : 0.46
% 2.07/1.26  Index Insertion      : 0.00
% 2.07/1.26  Index Deletion       : 0.00
% 2.07/1.26  Index Matching       : 0.00
% 2.07/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
