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
% DateTime   : Thu Dec  3 10:18:27 EST 2020

% Result     : Theorem 5.96s
% Output     : CNFRefutation 6.16s
% Verified   : 
% Statistics : Number of formulae       :   42 (  58 expanded)
%              Number of leaves         :   17 (  29 expanded)
%              Depth                    :   12
%              Number of atoms          :   90 ( 154 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_finset_1 > k2_zfmisc_1 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_finset_1,type,(
    v1_finset_1: $i > $o )).

tff(f_69,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( v1_finset_1(A)
          & r1_tarski(A,k2_zfmisc_1(B,C))
          & ! [D] :
              ~ ( v1_finset_1(D)
                & r1_tarski(D,B)
                & r1_tarski(A,k2_zfmisc_1(D,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_finset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ~ ( v1_finset_1(A)
        & r1_tarski(A,k2_zfmisc_1(B,C))
        & ! [D,E] :
            ~ ( v1_finset_1(D)
              & r1_tarski(D,B)
              & v1_finset_1(E)
              & r1_tarski(E,C)
              & r1_tarski(A,k2_zfmisc_1(D,E)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_finset_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_26,plain,(
    v1_finset_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_24,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_78,plain,(
    ! [A_39,B_40,C_41] :
      ( v1_finset_1('#skF_2'(A_39,B_40,C_41))
      | ~ r1_tarski(A_39,k2_zfmisc_1(B_40,C_41))
      | ~ v1_finset_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_91,plain,
    ( v1_finset_1('#skF_2'('#skF_4','#skF_5','#skF_6'))
    | ~ v1_finset_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_78])).

tff(c_97,plain,(
    v1_finset_1('#skF_2'('#skF_4','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_91])).

tff(c_14,plain,(
    ! [A_9,B_10,C_11] :
      ( r1_tarski('#skF_3'(A_9,B_10,C_11),C_11)
      | ~ r1_tarski(A_9,k2_zfmisc_1(B_10,C_11))
      | ~ v1_finset_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_18,plain,(
    ! [A_9,B_10,C_11] :
      ( r1_tarski('#skF_2'(A_9,B_10,C_11),B_10)
      | ~ r1_tarski(A_9,k2_zfmisc_1(B_10,C_11))
      | ~ v1_finset_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_12,plain,(
    ! [A_9,B_10,C_11] :
      ( r1_tarski(A_9,k2_zfmisc_1('#skF_2'(A_9,B_10,C_11),'#skF_3'(A_9,B_10,C_11)))
      | ~ r1_tarski(A_9,k2_zfmisc_1(B_10,C_11))
      | ~ v1_finset_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_8,plain,(
    ! [C_8,A_6,B_7] :
      ( r1_tarski(k2_zfmisc_1(C_8,A_6),k2_zfmisc_1(C_8,B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_35,plain,(
    ! [C_21,B_22,A_23] :
      ( r2_hidden(C_21,B_22)
      | ~ r2_hidden(C_21,A_23)
      | ~ r1_tarski(A_23,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_48,plain,(
    ! [A_31,B_32,B_33] :
      ( r2_hidden('#skF_1'(A_31,B_32),B_33)
      | ~ r1_tarski(A_31,B_33)
      | r1_tarski(A_31,B_32) ) ),
    inference(resolution,[status(thm)],[c_6,c_35])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_134,plain,(
    ! [A_65,B_66,B_67,B_68] :
      ( r2_hidden('#skF_1'(A_65,B_66),B_67)
      | ~ r1_tarski(B_68,B_67)
      | ~ r1_tarski(A_65,B_68)
      | r1_tarski(A_65,B_66) ) ),
    inference(resolution,[status(thm)],[c_48,c_2])).

tff(c_498,plain,(
    ! [B_143,A_144,A_146,C_142,B_145] :
      ( r2_hidden('#skF_1'(A_144,B_143),k2_zfmisc_1(C_142,B_145))
      | ~ r1_tarski(A_144,k2_zfmisc_1(C_142,A_146))
      | r1_tarski(A_144,B_143)
      | ~ r1_tarski(A_146,B_145) ) ),
    inference(resolution,[status(thm)],[c_8,c_134])).

tff(c_2902,plain,(
    ! [B_435,B_436,B_437,A_439,C_438] :
      ( r2_hidden('#skF_1'(A_439,B_435),k2_zfmisc_1('#skF_2'(A_439,B_437,C_438),B_436))
      | r1_tarski(A_439,B_435)
      | ~ r1_tarski('#skF_3'(A_439,B_437,C_438),B_436)
      | ~ r1_tarski(A_439,k2_zfmisc_1(B_437,C_438))
      | ~ v1_finset_1(A_439) ) ),
    inference(resolution,[status(thm)],[c_12,c_498])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2911,plain,(
    ! [A_440,B_441,C_442,B_443] :
      ( r1_tarski(A_440,k2_zfmisc_1('#skF_2'(A_440,B_441,C_442),B_443))
      | ~ r1_tarski('#skF_3'(A_440,B_441,C_442),B_443)
      | ~ r1_tarski(A_440,k2_zfmisc_1(B_441,C_442))
      | ~ v1_finset_1(A_440) ) ),
    inference(resolution,[status(thm)],[c_2902,c_4])).

tff(c_22,plain,(
    ! [D_15] :
      ( ~ r1_tarski('#skF_4',k2_zfmisc_1(D_15,'#skF_6'))
      | ~ r1_tarski(D_15,'#skF_5')
      | ~ v1_finset_1(D_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2997,plain,(
    ! [B_441,C_442] :
      ( ~ r1_tarski('#skF_2'('#skF_4',B_441,C_442),'#skF_5')
      | ~ v1_finset_1('#skF_2'('#skF_4',B_441,C_442))
      | ~ r1_tarski('#skF_3'('#skF_4',B_441,C_442),'#skF_6')
      | ~ r1_tarski('#skF_4',k2_zfmisc_1(B_441,C_442))
      | ~ v1_finset_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2911,c_22])).

tff(c_3035,plain,(
    ! [B_452,C_453] :
      ( ~ r1_tarski('#skF_2'('#skF_4',B_452,C_453),'#skF_5')
      | ~ v1_finset_1('#skF_2'('#skF_4',B_452,C_453))
      | ~ r1_tarski('#skF_3'('#skF_4',B_452,C_453),'#skF_6')
      | ~ r1_tarski('#skF_4',k2_zfmisc_1(B_452,C_453)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2997])).

tff(c_3039,plain,(
    ! [C_11] :
      ( ~ v1_finset_1('#skF_2'('#skF_4','#skF_5',C_11))
      | ~ r1_tarski('#skF_3'('#skF_4','#skF_5',C_11),'#skF_6')
      | ~ r1_tarski('#skF_4',k2_zfmisc_1('#skF_5',C_11))
      | ~ v1_finset_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_18,c_3035])).

tff(c_3043,plain,(
    ! [C_454] :
      ( ~ v1_finset_1('#skF_2'('#skF_4','#skF_5',C_454))
      | ~ r1_tarski('#skF_3'('#skF_4','#skF_5',C_454),'#skF_6')
      | ~ r1_tarski('#skF_4',k2_zfmisc_1('#skF_5',C_454)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_3039])).

tff(c_3047,plain,
    ( ~ v1_finset_1('#skF_2'('#skF_4','#skF_5','#skF_6'))
    | ~ r1_tarski('#skF_4',k2_zfmisc_1('#skF_5','#skF_6'))
    | ~ v1_finset_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_3043])).

tff(c_3051,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_97,c_3047])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:13:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.96/2.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.96/2.29  
% 5.96/2.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.96/2.29  %$ r2_hidden > r1_tarski > v1_finset_1 > k2_zfmisc_1 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 5.96/2.29  
% 5.96/2.29  %Foreground sorts:
% 5.96/2.29  
% 5.96/2.29  
% 5.96/2.29  %Background operators:
% 5.96/2.29  
% 5.96/2.29  
% 5.96/2.29  %Foreground operators:
% 5.96/2.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.96/2.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.96/2.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.96/2.29  tff('#skF_5', type, '#skF_5': $i).
% 5.96/2.29  tff('#skF_6', type, '#skF_6': $i).
% 5.96/2.29  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.96/2.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.96/2.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.96/2.29  tff('#skF_4', type, '#skF_4': $i).
% 5.96/2.29  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.96/2.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.96/2.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.96/2.29  tff(v1_finset_1, type, v1_finset_1: $i > $o).
% 5.96/2.29  
% 6.16/2.30  tff(f_69, negated_conjecture, ~(![A, B, C]: ~((v1_finset_1(A) & r1_tarski(A, k2_zfmisc_1(B, C))) & (![D]: ~((v1_finset_1(D) & r1_tarski(D, B)) & r1_tarski(A, k2_zfmisc_1(D, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_finset_1)).
% 6.16/2.30  tff(f_55, axiom, (![A, B, C]: ~((v1_finset_1(A) & r1_tarski(A, k2_zfmisc_1(B, C))) & (![D, E]: ~((((v1_finset_1(D) & r1_tarski(D, B)) & v1_finset_1(E)) & r1_tarski(E, C)) & r1_tarski(A, k2_zfmisc_1(D, E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_finset_1)).
% 6.16/2.30  tff(f_38, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 6.16/2.30  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.16/2.30  tff(c_26, plain, (v1_finset_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.16/2.30  tff(c_24, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.16/2.30  tff(c_78, plain, (![A_39, B_40, C_41]: (v1_finset_1('#skF_2'(A_39, B_40, C_41)) | ~r1_tarski(A_39, k2_zfmisc_1(B_40, C_41)) | ~v1_finset_1(A_39))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.16/2.30  tff(c_91, plain, (v1_finset_1('#skF_2'('#skF_4', '#skF_5', '#skF_6')) | ~v1_finset_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_78])).
% 6.16/2.30  tff(c_97, plain, (v1_finset_1('#skF_2'('#skF_4', '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_91])).
% 6.16/2.30  tff(c_14, plain, (![A_9, B_10, C_11]: (r1_tarski('#skF_3'(A_9, B_10, C_11), C_11) | ~r1_tarski(A_9, k2_zfmisc_1(B_10, C_11)) | ~v1_finset_1(A_9))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.16/2.30  tff(c_18, plain, (![A_9, B_10, C_11]: (r1_tarski('#skF_2'(A_9, B_10, C_11), B_10) | ~r1_tarski(A_9, k2_zfmisc_1(B_10, C_11)) | ~v1_finset_1(A_9))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.16/2.30  tff(c_12, plain, (![A_9, B_10, C_11]: (r1_tarski(A_9, k2_zfmisc_1('#skF_2'(A_9, B_10, C_11), '#skF_3'(A_9, B_10, C_11))) | ~r1_tarski(A_9, k2_zfmisc_1(B_10, C_11)) | ~v1_finset_1(A_9))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.16/2.30  tff(c_8, plain, (![C_8, A_6, B_7]: (r1_tarski(k2_zfmisc_1(C_8, A_6), k2_zfmisc_1(C_8, B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.16/2.30  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.16/2.30  tff(c_35, plain, (![C_21, B_22, A_23]: (r2_hidden(C_21, B_22) | ~r2_hidden(C_21, A_23) | ~r1_tarski(A_23, B_22))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.16/2.30  tff(c_48, plain, (![A_31, B_32, B_33]: (r2_hidden('#skF_1'(A_31, B_32), B_33) | ~r1_tarski(A_31, B_33) | r1_tarski(A_31, B_32))), inference(resolution, [status(thm)], [c_6, c_35])).
% 6.16/2.30  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.16/2.30  tff(c_134, plain, (![A_65, B_66, B_67, B_68]: (r2_hidden('#skF_1'(A_65, B_66), B_67) | ~r1_tarski(B_68, B_67) | ~r1_tarski(A_65, B_68) | r1_tarski(A_65, B_66))), inference(resolution, [status(thm)], [c_48, c_2])).
% 6.16/2.30  tff(c_498, plain, (![B_143, A_144, A_146, C_142, B_145]: (r2_hidden('#skF_1'(A_144, B_143), k2_zfmisc_1(C_142, B_145)) | ~r1_tarski(A_144, k2_zfmisc_1(C_142, A_146)) | r1_tarski(A_144, B_143) | ~r1_tarski(A_146, B_145))), inference(resolution, [status(thm)], [c_8, c_134])).
% 6.16/2.30  tff(c_2902, plain, (![B_435, B_436, B_437, A_439, C_438]: (r2_hidden('#skF_1'(A_439, B_435), k2_zfmisc_1('#skF_2'(A_439, B_437, C_438), B_436)) | r1_tarski(A_439, B_435) | ~r1_tarski('#skF_3'(A_439, B_437, C_438), B_436) | ~r1_tarski(A_439, k2_zfmisc_1(B_437, C_438)) | ~v1_finset_1(A_439))), inference(resolution, [status(thm)], [c_12, c_498])).
% 6.16/2.30  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.16/2.30  tff(c_2911, plain, (![A_440, B_441, C_442, B_443]: (r1_tarski(A_440, k2_zfmisc_1('#skF_2'(A_440, B_441, C_442), B_443)) | ~r1_tarski('#skF_3'(A_440, B_441, C_442), B_443) | ~r1_tarski(A_440, k2_zfmisc_1(B_441, C_442)) | ~v1_finset_1(A_440))), inference(resolution, [status(thm)], [c_2902, c_4])).
% 6.16/2.30  tff(c_22, plain, (![D_15]: (~r1_tarski('#skF_4', k2_zfmisc_1(D_15, '#skF_6')) | ~r1_tarski(D_15, '#skF_5') | ~v1_finset_1(D_15))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.16/2.30  tff(c_2997, plain, (![B_441, C_442]: (~r1_tarski('#skF_2'('#skF_4', B_441, C_442), '#skF_5') | ~v1_finset_1('#skF_2'('#skF_4', B_441, C_442)) | ~r1_tarski('#skF_3'('#skF_4', B_441, C_442), '#skF_6') | ~r1_tarski('#skF_4', k2_zfmisc_1(B_441, C_442)) | ~v1_finset_1('#skF_4'))), inference(resolution, [status(thm)], [c_2911, c_22])).
% 6.16/2.30  tff(c_3035, plain, (![B_452, C_453]: (~r1_tarski('#skF_2'('#skF_4', B_452, C_453), '#skF_5') | ~v1_finset_1('#skF_2'('#skF_4', B_452, C_453)) | ~r1_tarski('#skF_3'('#skF_4', B_452, C_453), '#skF_6') | ~r1_tarski('#skF_4', k2_zfmisc_1(B_452, C_453)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_2997])).
% 6.16/2.30  tff(c_3039, plain, (![C_11]: (~v1_finset_1('#skF_2'('#skF_4', '#skF_5', C_11)) | ~r1_tarski('#skF_3'('#skF_4', '#skF_5', C_11), '#skF_6') | ~r1_tarski('#skF_4', k2_zfmisc_1('#skF_5', C_11)) | ~v1_finset_1('#skF_4'))), inference(resolution, [status(thm)], [c_18, c_3035])).
% 6.16/2.30  tff(c_3043, plain, (![C_454]: (~v1_finset_1('#skF_2'('#skF_4', '#skF_5', C_454)) | ~r1_tarski('#skF_3'('#skF_4', '#skF_5', C_454), '#skF_6') | ~r1_tarski('#skF_4', k2_zfmisc_1('#skF_5', C_454)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_3039])).
% 6.16/2.30  tff(c_3047, plain, (~v1_finset_1('#skF_2'('#skF_4', '#skF_5', '#skF_6')) | ~r1_tarski('#skF_4', k2_zfmisc_1('#skF_5', '#skF_6')) | ~v1_finset_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_3043])).
% 6.16/2.30  tff(c_3051, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_97, c_3047])).
% 6.16/2.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.16/2.30  
% 6.16/2.30  Inference rules
% 6.16/2.30  ----------------------
% 6.16/2.30  #Ref     : 0
% 6.16/2.30  #Sup     : 812
% 6.16/2.30  #Fact    : 0
% 6.16/2.30  #Define  : 0
% 6.16/2.30  #Split   : 9
% 6.16/2.30  #Chain   : 0
% 6.16/2.30  #Close   : 0
% 6.16/2.30  
% 6.16/2.30  Ordering : KBO
% 6.16/2.30  
% 6.16/2.30  Simplification rules
% 6.16/2.30  ----------------------
% 6.16/2.30  #Subsume      : 271
% 6.16/2.30  #Demod        : 26
% 6.16/2.30  #Tautology    : 1
% 6.16/2.30  #SimpNegUnit  : 0
% 6.16/2.30  #BackRed      : 0
% 6.16/2.30  
% 6.16/2.30  #Partial instantiations: 0
% 6.16/2.30  #Strategies tried      : 1
% 6.16/2.30  
% 6.16/2.31  Timing (in seconds)
% 6.16/2.31  ----------------------
% 6.16/2.31  Preprocessing        : 0.27
% 6.16/2.31  Parsing              : 0.15
% 6.16/2.31  CNF conversion       : 0.02
% 6.16/2.31  Main loop            : 1.27
% 6.16/2.31  Inferencing          : 0.37
% 6.16/2.31  Reduction            : 0.25
% 6.16/2.31  Demodulation         : 0.16
% 6.16/2.31  BG Simplification    : 0.03
% 6.16/2.31  Subsumption          : 0.55
% 6.16/2.31  Abstraction          : 0.04
% 6.16/2.31  MUC search           : 0.00
% 6.16/2.31  Cooper               : 0.00
% 6.16/2.31  Total                : 1.57
% 6.16/2.31  Index Insertion      : 0.00
% 6.16/2.31  Index Deletion       : 0.00
% 6.16/2.31  Index Matching       : 0.00
% 6.16/2.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
