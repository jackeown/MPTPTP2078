%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:49 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   46 (  95 expanded)
%              Number of leaves         :   21 (  46 expanded)
%              Depth                    :    7
%              Number of atoms          :   71 ( 330 expanded)
%              Number of equality atoms :   29 (  97 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( v2_funct_1(B)
         => ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A)
                & k1_funct_1(B,C) = k1_funct_1(B,D) )
             => C = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_funct_2)).

tff(f_48,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(D)
          & r2_hidden(C,A) )
       => ( B = k1_xboole_0
          | k1_funct_1(k2_funct_1(D),k1_funct_1(D,C)) = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(c_26,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_24,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_20,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_22,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_16,plain,(
    r2_hidden('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_72,plain,(
    ! [D_18,C_19,B_20,A_21] :
      ( k1_funct_1(k2_funct_1(D_18),k1_funct_1(D_18,C_19)) = C_19
      | k1_xboole_0 = B_20
      | ~ r2_hidden(C_19,A_21)
      | ~ v2_funct_1(D_18)
      | ~ m1_subset_1(D_18,k1_zfmisc_1(k2_zfmisc_1(A_21,B_20)))
      | ~ v1_funct_2(D_18,A_21,B_20)
      | ~ v1_funct_1(D_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_79,plain,(
    ! [D_22,B_23] :
      ( k1_funct_1(k2_funct_1(D_22),k1_funct_1(D_22,'#skF_4')) = '#skF_4'
      | k1_xboole_0 = B_23
      | ~ v2_funct_1(D_22)
      | ~ m1_subset_1(D_22,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_23)))
      | ~ v1_funct_2(D_22,'#skF_1',B_23)
      | ~ v1_funct_1(D_22) ) ),
    inference(resolution,[status(thm)],[c_16,c_72])).

tff(c_81,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_4'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_79])).

tff(c_87,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_4'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_20,c_81])).

tff(c_89,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_87])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_49,plain,(
    ! [A_13,B_14] : ~ r2_hidden(A_13,k2_zfmisc_1(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_55,plain,(
    ! [A_1] : ~ r2_hidden(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_49])).

tff(c_93,plain,(
    ! [A_1] : ~ r2_hidden(A_1,'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_55])).

tff(c_102,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_16])).

tff(c_104,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_12,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_103,plain,(
    k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_14,plain,(
    k1_funct_1('#skF_2','#skF_3') = k1_funct_1('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_18,plain,(
    r2_hidden('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_105,plain,(
    ! [D_24,B_25] :
      ( k1_funct_1(k2_funct_1(D_24),k1_funct_1(D_24,'#skF_3')) = '#skF_3'
      | k1_xboole_0 = B_25
      | ~ v2_funct_1(D_24)
      | ~ m1_subset_1(D_24,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_25)))
      | ~ v1_funct_2(D_24,'#skF_1',B_25)
      | ~ v1_funct_1(D_24) ) ),
    inference(resolution,[status(thm)],[c_18,c_72])).

tff(c_107,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_3')) = '#skF_3'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_105])).

tff(c_113,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_20,c_14,c_107])).

tff(c_119,plain,
    ( '#skF_3' = '#skF_4'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_113])).

tff(c_120,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_12,c_119])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:05:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.16  
% 1.86/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.17  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.86/1.17  
% 1.86/1.17  %Foreground sorts:
% 1.86/1.17  
% 1.86/1.17  
% 1.86/1.17  %Background operators:
% 1.86/1.17  
% 1.86/1.17  
% 1.86/1.17  %Foreground operators:
% 1.86/1.17  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.86/1.17  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 1.86/1.17  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.86/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.86/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.86/1.17  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.86/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.86/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.86/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.86/1.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.86/1.17  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.86/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.86/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.86/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.86/1.17  
% 1.86/1.18  tff(f_66, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) => (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_funct_2)).
% 1.86/1.18  tff(f_48, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(D) & r2_hidden(C, A)) => ((B = k1_xboole_0) | (k1_funct_1(k2_funct_1(D), k1_funct_1(D, C)) = C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_funct_2)).
% 1.86/1.18  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.86/1.18  tff(f_34, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.86/1.18  tff(c_26, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.86/1.18  tff(c_24, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.86/1.18  tff(c_20, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.86/1.18  tff(c_22, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.86/1.18  tff(c_16, plain, (r2_hidden('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.86/1.18  tff(c_72, plain, (![D_18, C_19, B_20, A_21]: (k1_funct_1(k2_funct_1(D_18), k1_funct_1(D_18, C_19))=C_19 | k1_xboole_0=B_20 | ~r2_hidden(C_19, A_21) | ~v2_funct_1(D_18) | ~m1_subset_1(D_18, k1_zfmisc_1(k2_zfmisc_1(A_21, B_20))) | ~v1_funct_2(D_18, A_21, B_20) | ~v1_funct_1(D_18))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.86/1.18  tff(c_79, plain, (![D_22, B_23]: (k1_funct_1(k2_funct_1(D_22), k1_funct_1(D_22, '#skF_4'))='#skF_4' | k1_xboole_0=B_23 | ~v2_funct_1(D_22) | ~m1_subset_1(D_22, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_23))) | ~v1_funct_2(D_22, '#skF_1', B_23) | ~v1_funct_1(D_22))), inference(resolution, [status(thm)], [c_16, c_72])).
% 1.86/1.18  tff(c_81, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_4' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_22, c_79])).
% 1.86/1.18  tff(c_87, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_4' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_20, c_81])).
% 1.86/1.18  tff(c_89, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_87])).
% 1.86/1.18  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.86/1.18  tff(c_49, plain, (![A_13, B_14]: (~r2_hidden(A_13, k2_zfmisc_1(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.86/1.18  tff(c_55, plain, (![A_1]: (~r2_hidden(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_49])).
% 1.86/1.18  tff(c_93, plain, (![A_1]: (~r2_hidden(A_1, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_55])).
% 1.86/1.18  tff(c_102, plain, $false, inference(negUnitSimplification, [status(thm)], [c_93, c_16])).
% 1.86/1.18  tff(c_104, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_87])).
% 1.86/1.18  tff(c_12, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.86/1.18  tff(c_103, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_4'), inference(splitRight, [status(thm)], [c_87])).
% 1.86/1.18  tff(c_14, plain, (k1_funct_1('#skF_2', '#skF_3')=k1_funct_1('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.86/1.18  tff(c_18, plain, (r2_hidden('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.86/1.18  tff(c_105, plain, (![D_24, B_25]: (k1_funct_1(k2_funct_1(D_24), k1_funct_1(D_24, '#skF_3'))='#skF_3' | k1_xboole_0=B_25 | ~v2_funct_1(D_24) | ~m1_subset_1(D_24, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_25))) | ~v1_funct_2(D_24, '#skF_1', B_25) | ~v1_funct_1(D_24))), inference(resolution, [status(thm)], [c_18, c_72])).
% 1.86/1.18  tff(c_107, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_3'))='#skF_3' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_22, c_105])).
% 1.86/1.18  tff(c_113, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_20, c_14, c_107])).
% 1.86/1.18  tff(c_119, plain, ('#skF_3'='#skF_4' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_103, c_113])).
% 1.86/1.18  tff(c_120, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_12, c_119])).
% 1.86/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.18  
% 1.86/1.18  Inference rules
% 1.86/1.18  ----------------------
% 1.86/1.18  #Ref     : 0
% 1.86/1.18  #Sup     : 22
% 1.86/1.18  #Fact    : 0
% 1.86/1.18  #Define  : 0
% 1.86/1.18  #Split   : 1
% 1.86/1.18  #Chain   : 0
% 1.86/1.18  #Close   : 0
% 1.86/1.18  
% 1.86/1.18  Ordering : KBO
% 1.86/1.18  
% 1.86/1.18  Simplification rules
% 1.86/1.18  ----------------------
% 1.86/1.18  #Subsume      : 1
% 1.86/1.18  #Demod        : 18
% 1.86/1.18  #Tautology    : 16
% 1.86/1.18  #SimpNegUnit  : 3
% 1.86/1.18  #BackRed      : 8
% 1.86/1.18  
% 1.86/1.18  #Partial instantiations: 0
% 1.86/1.18  #Strategies tried      : 1
% 1.86/1.18  
% 1.86/1.18  Timing (in seconds)
% 1.86/1.18  ----------------------
% 1.86/1.18  Preprocessing        : 0.29
% 1.86/1.18  Parsing              : 0.16
% 1.86/1.18  CNF conversion       : 0.02
% 1.86/1.18  Main loop            : 0.14
% 1.86/1.18  Inferencing          : 0.04
% 1.86/1.18  Reduction            : 0.05
% 1.86/1.18  Demodulation         : 0.03
% 1.86/1.18  BG Simplification    : 0.01
% 1.86/1.18  Subsumption          : 0.02
% 1.86/1.18  Abstraction          : 0.01
% 1.86/1.18  MUC search           : 0.00
% 1.86/1.18  Cooper               : 0.00
% 1.86/1.18  Total                : 0.45
% 1.86/1.18  Index Insertion      : 0.00
% 1.86/1.18  Index Deletion       : 0.00
% 1.86/1.18  Index Matching       : 0.00
% 1.86/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
