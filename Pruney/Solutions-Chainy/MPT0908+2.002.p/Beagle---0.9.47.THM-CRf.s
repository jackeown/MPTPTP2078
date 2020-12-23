%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:56 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   45 (  83 expanded)
%              Number of leaves         :   20 (  42 expanded)
%              Depth                    :    5
%              Number of atoms          :   89 ( 286 expanded)
%              Number of equality atoms :   74 ( 247 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
       => ~ ( A != k1_xboole_0
            & B != k1_xboole_0
            & C != k1_xboole_0
            & ? [E,F,G] :
                ( D = k3_mcart_1(E,F,G)
                & ~ ( k5_mcart_1(A,B,C,D) = E
                    & k6_mcart_1(A,B,C,D) = F
                    & k7_mcart_1(A,B,C,D) = G ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_mcart_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ? [D] :
            ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
            & ? [E,F,G] :
                ( D = k3_mcart_1(E,F,G)
                & ~ ( k5_mcart_1(A,B,C,D) = E
                    & k6_mcart_1(A,B,C,D) = F
                    & k7_mcart_1(A,B,C,D) = G ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_mcart_1)).

tff(c_18,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_16,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_14,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_10,plain,
    ( k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_7'
    | k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_6'
    | k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_54,plain,(
    k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_10])).

tff(c_20,plain,(
    m1_subset_1('#skF_4',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_12,plain,(
    k3_mcart_1('#skF_5','#skF_6','#skF_7') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_55,plain,(
    ! [A_36,G_33,F_32,B_34,E_31,C_35] :
      ( k5_mcart_1(A_36,B_34,C_35,k3_mcart_1(E_31,F_32,G_33)) = E_31
      | ~ m1_subset_1(k3_mcart_1(E_31,F_32,G_33),k3_zfmisc_1(A_36,B_34,C_35))
      | k1_xboole_0 = C_35
      | k1_xboole_0 = B_34
      | k1_xboole_0 = A_36 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_61,plain,(
    ! [A_36,B_34,C_35] :
      ( k5_mcart_1(A_36,B_34,C_35,k3_mcart_1('#skF_5','#skF_6','#skF_7')) = '#skF_5'
      | ~ m1_subset_1('#skF_4',k3_zfmisc_1(A_36,B_34,C_35))
      | k1_xboole_0 = C_35
      | k1_xboole_0 = B_34
      | k1_xboole_0 = A_36 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_55])).

tff(c_63,plain,(
    ! [A_37,B_38,C_39] :
      ( k5_mcart_1(A_37,B_38,C_39,'#skF_4') = '#skF_5'
      | ~ m1_subset_1('#skF_4',k3_zfmisc_1(A_37,B_38,C_39))
      | k1_xboole_0 = C_39
      | k1_xboole_0 = B_38
      | k1_xboole_0 = A_37 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_61])).

tff(c_69,plain,
    ( k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_5'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_20,c_63])).

tff(c_73,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_16,c_14,c_54,c_69])).

tff(c_74,plain,
    ( k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_6'
    | k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_10])).

tff(c_80,plain,(
    k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_121,plain,(
    ! [G_60,C_62,E_58,A_63,F_59,B_61] :
      ( k7_mcart_1(A_63,B_61,C_62,k3_mcart_1(E_58,F_59,G_60)) = G_60
      | ~ m1_subset_1(k3_mcart_1(E_58,F_59,G_60),k3_zfmisc_1(A_63,B_61,C_62))
      | k1_xboole_0 = C_62
      | k1_xboole_0 = B_61
      | k1_xboole_0 = A_63 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_127,plain,(
    ! [A_63,B_61,C_62] :
      ( k7_mcart_1(A_63,B_61,C_62,k3_mcart_1('#skF_5','#skF_6','#skF_7')) = '#skF_7'
      | ~ m1_subset_1('#skF_4',k3_zfmisc_1(A_63,B_61,C_62))
      | k1_xboole_0 = C_62
      | k1_xboole_0 = B_61
      | k1_xboole_0 = A_63 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_121])).

tff(c_129,plain,(
    ! [A_64,B_65,C_66] :
      ( k7_mcart_1(A_64,B_65,C_66,'#skF_4') = '#skF_7'
      | ~ m1_subset_1('#skF_4',k3_zfmisc_1(A_64,B_65,C_66))
      | k1_xboole_0 = C_66
      | k1_xboole_0 = B_65
      | k1_xboole_0 = A_64 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_127])).

tff(c_135,plain,
    ( k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_7'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_20,c_129])).

tff(c_139,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_16,c_14,c_80,c_135])).

tff(c_140,plain,(
    k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_182,plain,(
    ! [G_87,C_89,B_88,F_86,E_85,A_90] :
      ( k6_mcart_1(A_90,B_88,C_89,k3_mcart_1(E_85,F_86,G_87)) = F_86
      | ~ m1_subset_1(k3_mcart_1(E_85,F_86,G_87),k3_zfmisc_1(A_90,B_88,C_89))
      | k1_xboole_0 = C_89
      | k1_xboole_0 = B_88
      | k1_xboole_0 = A_90 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_188,plain,(
    ! [A_90,B_88,C_89] :
      ( k6_mcart_1(A_90,B_88,C_89,k3_mcart_1('#skF_5','#skF_6','#skF_7')) = '#skF_6'
      | ~ m1_subset_1('#skF_4',k3_zfmisc_1(A_90,B_88,C_89))
      | k1_xboole_0 = C_89
      | k1_xboole_0 = B_88
      | k1_xboole_0 = A_90 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_182])).

tff(c_190,plain,(
    ! [A_91,B_92,C_93] :
      ( k6_mcart_1(A_91,B_92,C_93,'#skF_4') = '#skF_6'
      | ~ m1_subset_1('#skF_4',k3_zfmisc_1(A_91,B_92,C_93))
      | k1_xboole_0 = C_93
      | k1_xboole_0 = B_92
      | k1_xboole_0 = A_91 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_188])).

tff(c_196,plain,
    ( k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_6'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_20,c_190])).

tff(c_200,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_16,c_14,c_140,c_196])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:43:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.19  
% 1.93/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.19  %$ m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.93/1.19  
% 1.93/1.19  %Foreground sorts:
% 1.93/1.19  
% 1.93/1.19  
% 1.93/1.19  %Background operators:
% 1.93/1.19  
% 1.93/1.19  
% 1.93/1.19  %Foreground operators:
% 1.93/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.93/1.19  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 1.93/1.19  tff('#skF_7', type, '#skF_7': $i).
% 1.93/1.19  tff('#skF_5', type, '#skF_5': $i).
% 1.93/1.19  tff('#skF_6', type, '#skF_6': $i).
% 1.93/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.93/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.93/1.19  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 1.93/1.19  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 1.93/1.19  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 1.93/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.93/1.19  tff('#skF_4', type, '#skF_4': $i).
% 1.93/1.19  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 1.93/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.93/1.19  
% 1.93/1.20  tff(f_73, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & (?[E, F, G]: ((D = k3_mcart_1(E, F, G)) & ~(((k5_mcart_1(A, B, C, D) = E) & (k6_mcart_1(A, B, C, D) = F)) & (k7_mcart_1(A, B, C, D) = G))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_mcart_1)).
% 1.93/1.20  tff(f_50, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & (?[D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) & (?[E, F, G]: ((D = k3_mcart_1(E, F, G)) & ~(((k5_mcart_1(A, B, C, D) = E) & (k6_mcart_1(A, B, C, D) = F)) & (k7_mcart_1(A, B, C, D) = G)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_mcart_1)).
% 1.93/1.20  tff(c_18, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.93/1.20  tff(c_16, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.93/1.20  tff(c_14, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.93/1.20  tff(c_10, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_7' | k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_6' | k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.93/1.20  tff(c_54, plain, (k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_5'), inference(splitLeft, [status(thm)], [c_10])).
% 1.93/1.20  tff(c_20, plain, (m1_subset_1('#skF_4', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.93/1.20  tff(c_12, plain, (k3_mcart_1('#skF_5', '#skF_6', '#skF_7')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.93/1.20  tff(c_55, plain, (![A_36, G_33, F_32, B_34, E_31, C_35]: (k5_mcart_1(A_36, B_34, C_35, k3_mcart_1(E_31, F_32, G_33))=E_31 | ~m1_subset_1(k3_mcart_1(E_31, F_32, G_33), k3_zfmisc_1(A_36, B_34, C_35)) | k1_xboole_0=C_35 | k1_xboole_0=B_34 | k1_xboole_0=A_36)), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.93/1.20  tff(c_61, plain, (![A_36, B_34, C_35]: (k5_mcart_1(A_36, B_34, C_35, k3_mcart_1('#skF_5', '#skF_6', '#skF_7'))='#skF_5' | ~m1_subset_1('#skF_4', k3_zfmisc_1(A_36, B_34, C_35)) | k1_xboole_0=C_35 | k1_xboole_0=B_34 | k1_xboole_0=A_36)), inference(superposition, [status(thm), theory('equality')], [c_12, c_55])).
% 1.93/1.20  tff(c_63, plain, (![A_37, B_38, C_39]: (k5_mcart_1(A_37, B_38, C_39, '#skF_4')='#skF_5' | ~m1_subset_1('#skF_4', k3_zfmisc_1(A_37, B_38, C_39)) | k1_xboole_0=C_39 | k1_xboole_0=B_38 | k1_xboole_0=A_37)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_61])).
% 1.93/1.20  tff(c_69, plain, (k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_5' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_20, c_63])).
% 1.93/1.20  tff(c_73, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_16, c_14, c_54, c_69])).
% 1.93/1.20  tff(c_74, plain, (k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_6' | k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_7'), inference(splitRight, [status(thm)], [c_10])).
% 1.93/1.20  tff(c_80, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_7'), inference(splitLeft, [status(thm)], [c_74])).
% 1.93/1.20  tff(c_121, plain, (![G_60, C_62, E_58, A_63, F_59, B_61]: (k7_mcart_1(A_63, B_61, C_62, k3_mcart_1(E_58, F_59, G_60))=G_60 | ~m1_subset_1(k3_mcart_1(E_58, F_59, G_60), k3_zfmisc_1(A_63, B_61, C_62)) | k1_xboole_0=C_62 | k1_xboole_0=B_61 | k1_xboole_0=A_63)), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.93/1.20  tff(c_127, plain, (![A_63, B_61, C_62]: (k7_mcart_1(A_63, B_61, C_62, k3_mcart_1('#skF_5', '#skF_6', '#skF_7'))='#skF_7' | ~m1_subset_1('#skF_4', k3_zfmisc_1(A_63, B_61, C_62)) | k1_xboole_0=C_62 | k1_xboole_0=B_61 | k1_xboole_0=A_63)), inference(superposition, [status(thm), theory('equality')], [c_12, c_121])).
% 1.93/1.20  tff(c_129, plain, (![A_64, B_65, C_66]: (k7_mcart_1(A_64, B_65, C_66, '#skF_4')='#skF_7' | ~m1_subset_1('#skF_4', k3_zfmisc_1(A_64, B_65, C_66)) | k1_xboole_0=C_66 | k1_xboole_0=B_65 | k1_xboole_0=A_64)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_127])).
% 1.93/1.20  tff(c_135, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_7' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_20, c_129])).
% 1.93/1.20  tff(c_139, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_16, c_14, c_80, c_135])).
% 1.93/1.20  tff(c_140, plain, (k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_74])).
% 1.93/1.20  tff(c_182, plain, (![G_87, C_89, B_88, F_86, E_85, A_90]: (k6_mcart_1(A_90, B_88, C_89, k3_mcart_1(E_85, F_86, G_87))=F_86 | ~m1_subset_1(k3_mcart_1(E_85, F_86, G_87), k3_zfmisc_1(A_90, B_88, C_89)) | k1_xboole_0=C_89 | k1_xboole_0=B_88 | k1_xboole_0=A_90)), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.93/1.20  tff(c_188, plain, (![A_90, B_88, C_89]: (k6_mcart_1(A_90, B_88, C_89, k3_mcart_1('#skF_5', '#skF_6', '#skF_7'))='#skF_6' | ~m1_subset_1('#skF_4', k3_zfmisc_1(A_90, B_88, C_89)) | k1_xboole_0=C_89 | k1_xboole_0=B_88 | k1_xboole_0=A_90)), inference(superposition, [status(thm), theory('equality')], [c_12, c_182])).
% 1.93/1.20  tff(c_190, plain, (![A_91, B_92, C_93]: (k6_mcart_1(A_91, B_92, C_93, '#skF_4')='#skF_6' | ~m1_subset_1('#skF_4', k3_zfmisc_1(A_91, B_92, C_93)) | k1_xboole_0=C_93 | k1_xboole_0=B_92 | k1_xboole_0=A_91)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_188])).
% 1.93/1.20  tff(c_196, plain, (k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_6' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_20, c_190])).
% 1.93/1.20  tff(c_200, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_16, c_14, c_140, c_196])).
% 1.93/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.20  
% 1.93/1.20  Inference rules
% 1.93/1.20  ----------------------
% 1.93/1.20  #Ref     : 0
% 1.93/1.20  #Sup     : 43
% 1.93/1.20  #Fact    : 0
% 1.93/1.20  #Define  : 0
% 1.93/1.20  #Split   : 2
% 1.93/1.20  #Chain   : 0
% 1.93/1.20  #Close   : 0
% 1.93/1.20  
% 1.93/1.20  Ordering : KBO
% 1.93/1.20  
% 1.93/1.20  Simplification rules
% 1.93/1.20  ----------------------
% 1.93/1.20  #Subsume      : 0
% 1.93/1.20  #Demod        : 13
% 1.93/1.20  #Tautology    : 17
% 1.93/1.20  #SimpNegUnit  : 7
% 1.93/1.20  #BackRed      : 0
% 1.93/1.20  
% 1.93/1.20  #Partial instantiations: 0
% 1.93/1.20  #Strategies tried      : 1
% 1.93/1.20  
% 1.93/1.20  Timing (in seconds)
% 1.93/1.20  ----------------------
% 1.93/1.21  Preprocessing        : 0.28
% 1.93/1.21  Parsing              : 0.14
% 1.93/1.21  CNF conversion       : 0.02
% 1.93/1.21  Main loop            : 0.17
% 1.93/1.21  Inferencing          : 0.07
% 1.93/1.21  Reduction            : 0.05
% 1.93/1.21  Demodulation         : 0.04
% 1.93/1.21  BG Simplification    : 0.01
% 1.93/1.21  Subsumption          : 0.02
% 1.93/1.21  Abstraction          : 0.01
% 1.93/1.21  MUC search           : 0.00
% 1.93/1.21  Cooper               : 0.00
% 1.93/1.21  Total                : 0.47
% 1.93/1.21  Index Insertion      : 0.00
% 1.93/1.21  Index Deletion       : 0.00
% 1.93/1.21  Index Matching       : 0.00
% 1.93/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
