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
% DateTime   : Thu Dec  3 10:09:21 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 141 expanded)
%              Number of leaves         :   22 (  54 expanded)
%              Depth                    :   10
%              Number of atoms          :   81 ( 320 expanded)
%              Number of equality atoms :   23 (  79 expanded)
%              Maximal formula depth    :   10 (   3 average)
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

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & ~ ! [C] :
                ( m1_subset_1(C,k2_zfmisc_1(A,B))
               => C = k4_tarski(k1_mcart_1(C),k2_mcart_1(C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_mcart_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_58,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_64,axiom,(
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

tff(f_56,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ~ v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_subset_1)).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_38,plain,(
    ! [B_17,A_18] :
      ( v1_xboole_0(B_17)
      | ~ m1_subset_1(B_17,A_18)
      | ~ v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_42,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_22,c_38])).

tff(c_43,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_20,plain,(
    k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_16,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( r2_hidden(B_4,A_3)
      | ~ m1_subset_1(B_4,A_3)
      | v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_56,plain,(
    ! [A_27,B_28] :
      ( k4_tarski(k1_mcart_1(A_27),k2_mcart_1(A_27)) = A_27
      | ~ r2_hidden(A_27,B_28)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_60,plain,(
    ! [B_29,A_30] :
      ( k4_tarski(k1_mcart_1(B_29),k2_mcart_1(B_29)) = B_29
      | ~ v1_relat_1(A_30)
      | ~ m1_subset_1(B_29,A_30)
      | v1_xboole_0(A_30) ) ),
    inference(resolution,[status(thm)],[c_8,c_56])).

tff(c_64,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2'))
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_22,c_60])).

tff(c_68,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3'
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_64])).

tff(c_70,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_20,c_68])).

tff(c_71,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_28,plain,(
    ! [B_14,A_15] :
      ( ~ v1_xboole_0(B_14)
      | B_14 = A_15
      | ~ v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_31,plain,(
    ! [A_15] :
      ( k1_xboole_0 = A_15
      | ~ v1_xboole_0(A_15) ) ),
    inference(resolution,[status(thm)],[c_2,c_28])).

tff(c_78,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_71,c_31])).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_82,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_24])).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_83,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_26])).

tff(c_72,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | B_2 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_92,plain,(
    ! [A_31] :
      ( A_31 = '#skF_3'
      | ~ v1_xboole_0(A_31) ) ),
    inference(resolution,[status(thm)],[c_71,c_4])).

tff(c_99,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_72,c_92])).

tff(c_129,plain,(
    ! [A_38,B_39] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_38,B_39))
      | v1_xboole_0(B_39)
      | v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_132,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_129])).

tff(c_134,plain,
    ( v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_132])).

tff(c_135,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_134])).

tff(c_79,plain,(
    ! [A_1] :
      ( A_1 = '#skF_3'
      | ~ v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_71,c_4])).

tff(c_138,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_135,c_79])).

tff(c_144,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_138])).

tff(c_145,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_149,plain,(
    '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_145,c_79])).

tff(c_155,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_149])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:37:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.21  
% 1.87/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.21  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.87/1.21  
% 1.87/1.21  %Foreground sorts:
% 1.87/1.21  
% 1.87/1.21  
% 1.87/1.21  %Background operators:
% 1.87/1.21  
% 1.87/1.21  
% 1.87/1.21  %Foreground operators:
% 1.87/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.87/1.21  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.87/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.87/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.87/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.87/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.87/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.21  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.87/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.87/1.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.87/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.21  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.87/1.21  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.87/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.87/1.21  
% 1.87/1.22  tff(f_78, negated_conjecture, ~(![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(![C]: (m1_subset_1(C, k2_zfmisc_1(A, B)) => (C = k4_tarski(k1_mcart_1(C), k2_mcart_1(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_mcart_1)).
% 1.87/1.22  tff(f_47, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 1.87/1.22  tff(f_58, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.87/1.22  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_mcart_1)).
% 1.87/1.22  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.87/1.22  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 1.87/1.22  tff(f_56, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => ~v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_subset_1)).
% 1.87/1.22  tff(c_22, plain, (m1_subset_1('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.87/1.22  tff(c_38, plain, (![B_17, A_18]: (v1_xboole_0(B_17) | ~m1_subset_1(B_17, A_18) | ~v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.87/1.22  tff(c_42, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_22, c_38])).
% 1.87/1.22  tff(c_43, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_42])).
% 1.87/1.22  tff(c_20, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.87/1.22  tff(c_16, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.87/1.22  tff(c_8, plain, (![B_4, A_3]: (r2_hidden(B_4, A_3) | ~m1_subset_1(B_4, A_3) | v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.87/1.22  tff(c_56, plain, (![A_27, B_28]: (k4_tarski(k1_mcart_1(A_27), k2_mcart_1(A_27))=A_27 | ~r2_hidden(A_27, B_28) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.87/1.22  tff(c_60, plain, (![B_29, A_30]: (k4_tarski(k1_mcart_1(B_29), k2_mcart_1(B_29))=B_29 | ~v1_relat_1(A_30) | ~m1_subset_1(B_29, A_30) | v1_xboole_0(A_30))), inference(resolution, [status(thm)], [c_8, c_56])).
% 1.87/1.22  tff(c_64, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3' | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2')) | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_22, c_60])).
% 1.87/1.22  tff(c_68, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3' | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_64])).
% 1.87/1.22  tff(c_70, plain, $false, inference(negUnitSimplification, [status(thm)], [c_43, c_20, c_68])).
% 1.87/1.22  tff(c_71, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_42])).
% 1.87/1.22  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.87/1.22  tff(c_28, plain, (![B_14, A_15]: (~v1_xboole_0(B_14) | B_14=A_15 | ~v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.87/1.22  tff(c_31, plain, (![A_15]: (k1_xboole_0=A_15 | ~v1_xboole_0(A_15))), inference(resolution, [status(thm)], [c_2, c_28])).
% 1.87/1.22  tff(c_78, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_71, c_31])).
% 1.87/1.22  tff(c_24, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.87/1.22  tff(c_82, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_24])).
% 1.87/1.22  tff(c_26, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.87/1.22  tff(c_83, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_26])).
% 1.87/1.22  tff(c_72, plain, (v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_42])).
% 1.87/1.22  tff(c_4, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | B_2=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.87/1.22  tff(c_92, plain, (![A_31]: (A_31='#skF_3' | ~v1_xboole_0(A_31))), inference(resolution, [status(thm)], [c_71, c_4])).
% 1.87/1.22  tff(c_99, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_72, c_92])).
% 1.87/1.22  tff(c_129, plain, (![A_38, B_39]: (~v1_xboole_0(k2_zfmisc_1(A_38, B_39)) | v1_xboole_0(B_39) | v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.87/1.22  tff(c_132, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_99, c_129])).
% 1.87/1.22  tff(c_134, plain, (v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_132])).
% 1.87/1.22  tff(c_135, plain, (v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_134])).
% 1.87/1.22  tff(c_79, plain, (![A_1]: (A_1='#skF_3' | ~v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_71, c_4])).
% 1.87/1.22  tff(c_138, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_135, c_79])).
% 1.87/1.22  tff(c_144, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83, c_138])).
% 1.87/1.22  tff(c_145, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_134])).
% 1.87/1.22  tff(c_149, plain, ('#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_145, c_79])).
% 1.87/1.22  tff(c_155, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_149])).
% 1.87/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.22  
% 1.87/1.22  Inference rules
% 1.87/1.22  ----------------------
% 1.87/1.22  #Ref     : 0
% 1.87/1.22  #Sup     : 26
% 1.87/1.22  #Fact    : 0
% 1.87/1.22  #Define  : 0
% 1.87/1.22  #Split   : 2
% 1.87/1.22  #Chain   : 0
% 1.87/1.22  #Close   : 0
% 1.87/1.22  
% 1.87/1.22  Ordering : KBO
% 1.87/1.22  
% 1.87/1.22  Simplification rules
% 1.87/1.22  ----------------------
% 1.87/1.22  #Subsume      : 2
% 1.87/1.22  #Demod        : 13
% 1.87/1.22  #Tautology    : 14
% 1.87/1.22  #SimpNegUnit  : 3
% 1.87/1.22  #BackRed      : 6
% 1.87/1.22  
% 1.87/1.22  #Partial instantiations: 0
% 1.87/1.22  #Strategies tried      : 1
% 1.87/1.22  
% 1.87/1.22  Timing (in seconds)
% 1.87/1.22  ----------------------
% 1.87/1.22  Preprocessing        : 0.27
% 1.87/1.22  Parsing              : 0.14
% 1.87/1.22  CNF conversion       : 0.02
% 1.87/1.22  Main loop            : 0.14
% 1.87/1.22  Inferencing          : 0.05
% 1.87/1.22  Reduction            : 0.04
% 1.87/1.22  Demodulation         : 0.03
% 1.87/1.22  BG Simplification    : 0.01
% 1.87/1.22  Subsumption          : 0.03
% 1.87/1.22  Abstraction          : 0.01
% 1.87/1.22  MUC search           : 0.00
% 1.87/1.23  Cooper               : 0.00
% 1.87/1.23  Total                : 0.44
% 1.87/1.23  Index Insertion      : 0.00
% 1.87/1.23  Index Deletion       : 0.00
% 1.87/1.23  Index Matching       : 0.00
% 1.87/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
