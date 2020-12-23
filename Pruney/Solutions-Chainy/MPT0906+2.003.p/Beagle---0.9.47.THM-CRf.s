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
% DateTime   : Thu Dec  3 10:09:54 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   55 (  73 expanded)
%              Number of leaves         :   23 (  35 expanded)
%              Depth                    :    7
%              Number of atoms          :   77 ( 122 expanded)
%              Number of equality atoms :   35 (  60 expanded)
%              Maximal formula depth    :    9 (   3 average)
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

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) != k1_xboole_0
       => ! [C] :
            ( m1_subset_1(C,k2_zfmisc_1(A,B))
           => ( C != k1_mcart_1(C)
              & C != k2_mcart_1(C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_mcart_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_51,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ( A != k1_mcart_1(A)
        & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_42,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(c_24,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_18,plain,(
    ! [A_14,B_15] : k2_mcart_1(k4_tarski(A_14,B_15)) = B_15 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_10,plain,(
    ! [B_10,C_11] : k2_mcart_1(k4_tarski(B_10,C_11)) != k4_tarski(B_10,C_11) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_26,plain,(
    ! [B_10,C_11] : k4_tarski(B_10,C_11) != C_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_10])).

tff(c_8,plain,(
    ! [A_5,B_6] : v1_relat_1(k2_zfmisc_1(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_16,plain,(
    ! [A_14,B_15] : k1_mcart_1(k4_tarski(A_14,B_15)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_12,plain,(
    ! [B_10,C_11] : k1_mcart_1(k4_tarski(B_10,C_11)) != k4_tarski(B_10,C_11) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_25,plain,(
    ! [B_10,C_11] : k4_tarski(B_10,C_11) != B_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_12])).

tff(c_20,plain,
    ( k2_mcart_1('#skF_3') = '#skF_3'
    | k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_48,plain,(
    k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_64,plain,(
    ! [A_32,B_33] :
      ( k4_tarski(k1_mcart_1(A_32),k2_mcart_1(A_32)) = A_32
      | ~ r2_hidden(A_32,B_33)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_68,plain,(
    ! [A_34,B_35] :
      ( k4_tarski(k1_mcart_1(A_34),k2_mcart_1(A_34)) = A_34
      | ~ v1_relat_1(B_35)
      | v1_xboole_0(B_35)
      | ~ m1_subset_1(A_34,B_35) ) ),
    inference(resolution,[status(thm)],[c_6,c_64])).

tff(c_70,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2'))
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_22,c_68])).

tff(c_73,plain,
    ( k4_tarski('#skF_3',k2_mcart_1('#skF_3')) = '#skF_3'
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_48,c_70])).

tff(c_74,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_25,c_73])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_53,plain,(
    ! [B_27,A_28] :
      ( ~ v1_xboole_0(B_27)
      | B_27 = A_28
      | ~ v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_56,plain,(
    ! [A_28] :
      ( k1_xboole_0 = A_28
      | ~ v1_xboole_0(A_28) ) ),
    inference(resolution,[status(thm)],[c_2,c_53])).

tff(c_77,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_74,c_56])).

tff(c_83,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_77])).

tff(c_84,plain,(
    k2_mcart_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_101,plain,(
    ! [A_41,B_42] :
      ( k4_tarski(k1_mcart_1(A_41),k2_mcart_1(A_41)) = A_41
      | ~ r2_hidden(A_41,B_42)
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_105,plain,(
    ! [A_43,B_44] :
      ( k4_tarski(k1_mcart_1(A_43),k2_mcart_1(A_43)) = A_43
      | ~ v1_relat_1(B_44)
      | v1_xboole_0(B_44)
      | ~ m1_subset_1(A_43,B_44) ) ),
    inference(resolution,[status(thm)],[c_6,c_101])).

tff(c_107,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2'))
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_22,c_105])).

tff(c_110,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),'#skF_3') = '#skF_3'
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_84,c_107])).

tff(c_111,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_110])).

tff(c_90,plain,(
    ! [B_36,A_37] :
      ( ~ v1_xboole_0(B_36)
      | B_36 = A_37
      | ~ v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_93,plain,(
    ! [A_37] :
      ( k1_xboole_0 = A_37
      | ~ v1_xboole_0(A_37) ) ),
    inference(resolution,[status(thm)],[c_2,c_90])).

tff(c_114,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_111,c_93])).

tff(c_120,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_114])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:37:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.61/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.16  
% 1.61/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.17  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.61/1.17  
% 1.61/1.17  %Foreground sorts:
% 1.61/1.17  
% 1.61/1.17  
% 1.61/1.17  %Background operators:
% 1.61/1.17  
% 1.61/1.17  
% 1.61/1.17  %Foreground operators:
% 1.61/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.61/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.61/1.17  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.61/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.61/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.61/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.61/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.61/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.61/1.17  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.61/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.61/1.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.61/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.61/1.17  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.61/1.17  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.61/1.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.61/1.17  
% 1.61/1.18  tff(f_74, negated_conjecture, ~(![A, B]: (~(k2_zfmisc_1(A, B) = k1_xboole_0) => (![C]: (m1_subset_1(C, k2_zfmisc_1(A, B)) => (~(C = k1_mcart_1(C)) & ~(C = k2_mcart_1(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_mcart_1)).
% 1.61/1.18  tff(f_61, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 1.61/1.18  tff(f_51, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 1.61/1.18  tff(f_42, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.61/1.18  tff(f_40, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 1.61/1.18  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_mcart_1)).
% 1.61/1.18  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.61/1.18  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 1.61/1.18  tff(c_24, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.61/1.18  tff(c_18, plain, (![A_14, B_15]: (k2_mcart_1(k4_tarski(A_14, B_15))=B_15)), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.61/1.18  tff(c_10, plain, (![B_10, C_11]: (k2_mcart_1(k4_tarski(B_10, C_11))!=k4_tarski(B_10, C_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.61/1.18  tff(c_26, plain, (![B_10, C_11]: (k4_tarski(B_10, C_11)!=C_11)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_10])).
% 1.61/1.18  tff(c_8, plain, (![A_5, B_6]: (v1_relat_1(k2_zfmisc_1(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.61/1.18  tff(c_16, plain, (![A_14, B_15]: (k1_mcart_1(k4_tarski(A_14, B_15))=A_14)), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.61/1.18  tff(c_12, plain, (![B_10, C_11]: (k1_mcart_1(k4_tarski(B_10, C_11))!=k4_tarski(B_10, C_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.61/1.18  tff(c_25, plain, (![B_10, C_11]: (k4_tarski(B_10, C_11)!=B_10)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_12])).
% 1.61/1.18  tff(c_20, plain, (k2_mcart_1('#skF_3')='#skF_3' | k1_mcart_1('#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.61/1.18  tff(c_48, plain, (k1_mcart_1('#skF_3')='#skF_3'), inference(splitLeft, [status(thm)], [c_20])).
% 1.61/1.18  tff(c_22, plain, (m1_subset_1('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.61/1.18  tff(c_6, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.61/1.18  tff(c_64, plain, (![A_32, B_33]: (k4_tarski(k1_mcart_1(A_32), k2_mcart_1(A_32))=A_32 | ~r2_hidden(A_32, B_33) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.61/1.18  tff(c_68, plain, (![A_34, B_35]: (k4_tarski(k1_mcart_1(A_34), k2_mcart_1(A_34))=A_34 | ~v1_relat_1(B_35) | v1_xboole_0(B_35) | ~m1_subset_1(A_34, B_35))), inference(resolution, [status(thm)], [c_6, c_64])).
% 1.61/1.18  tff(c_70, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3' | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2')) | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_22, c_68])).
% 1.61/1.18  tff(c_73, plain, (k4_tarski('#skF_3', k2_mcart_1('#skF_3'))='#skF_3' | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_48, c_70])).
% 1.61/1.18  tff(c_74, plain, (v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_25, c_73])).
% 1.61/1.18  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.61/1.18  tff(c_53, plain, (![B_27, A_28]: (~v1_xboole_0(B_27) | B_27=A_28 | ~v1_xboole_0(A_28))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.61/1.18  tff(c_56, plain, (![A_28]: (k1_xboole_0=A_28 | ~v1_xboole_0(A_28))), inference(resolution, [status(thm)], [c_2, c_53])).
% 1.61/1.18  tff(c_77, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_74, c_56])).
% 1.61/1.18  tff(c_83, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_77])).
% 1.61/1.18  tff(c_84, plain, (k2_mcart_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_20])).
% 1.61/1.18  tff(c_101, plain, (![A_41, B_42]: (k4_tarski(k1_mcart_1(A_41), k2_mcart_1(A_41))=A_41 | ~r2_hidden(A_41, B_42) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.61/1.18  tff(c_105, plain, (![A_43, B_44]: (k4_tarski(k1_mcart_1(A_43), k2_mcart_1(A_43))=A_43 | ~v1_relat_1(B_44) | v1_xboole_0(B_44) | ~m1_subset_1(A_43, B_44))), inference(resolution, [status(thm)], [c_6, c_101])).
% 1.61/1.18  tff(c_107, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3' | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2')) | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_22, c_105])).
% 1.61/1.18  tff(c_110, plain, (k4_tarski(k1_mcart_1('#skF_3'), '#skF_3')='#skF_3' | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_84, c_107])).
% 1.61/1.18  tff(c_111, plain, (v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_26, c_110])).
% 1.61/1.18  tff(c_90, plain, (![B_36, A_37]: (~v1_xboole_0(B_36) | B_36=A_37 | ~v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.61/1.18  tff(c_93, plain, (![A_37]: (k1_xboole_0=A_37 | ~v1_xboole_0(A_37))), inference(resolution, [status(thm)], [c_2, c_90])).
% 1.61/1.18  tff(c_114, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_111, c_93])).
% 1.61/1.18  tff(c_120, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_114])).
% 1.61/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.18  
% 1.61/1.18  Inference rules
% 1.61/1.18  ----------------------
% 1.61/1.18  #Ref     : 0
% 1.61/1.18  #Sup     : 20
% 1.61/1.18  #Fact    : 0
% 1.61/1.18  #Define  : 0
% 1.61/1.18  #Split   : 1
% 1.61/1.18  #Chain   : 0
% 1.61/1.18  #Close   : 0
% 1.61/1.18  
% 1.61/1.18  Ordering : KBO
% 1.61/1.18  
% 1.61/1.18  Simplification rules
% 1.61/1.18  ----------------------
% 1.61/1.18  #Subsume      : 0
% 1.61/1.18  #Demod        : 6
% 1.61/1.18  #Tautology    : 10
% 1.61/1.18  #SimpNegUnit  : 4
% 1.61/1.18  #BackRed      : 0
% 1.61/1.18  
% 1.61/1.18  #Partial instantiations: 0
% 1.61/1.18  #Strategies tried      : 1
% 1.61/1.18  
% 1.61/1.18  Timing (in seconds)
% 1.61/1.18  ----------------------
% 1.88/1.18  Preprocessing        : 0.28
% 1.88/1.18  Parsing              : 0.16
% 1.88/1.18  CNF conversion       : 0.02
% 1.88/1.18  Main loop            : 0.13
% 1.88/1.18  Inferencing          : 0.05
% 1.88/1.18  Reduction            : 0.04
% 1.88/1.18  Demodulation         : 0.03
% 1.88/1.18  BG Simplification    : 0.01
% 1.88/1.18  Subsumption          : 0.02
% 1.88/1.18  Abstraction          : 0.01
% 1.88/1.18  MUC search           : 0.00
% 1.88/1.18  Cooper               : 0.00
% 1.88/1.18  Total                : 0.44
% 1.88/1.18  Index Insertion      : 0.00
% 1.88/1.18  Index Deletion       : 0.00
% 1.88/1.18  Index Matching       : 0.00
% 1.88/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
