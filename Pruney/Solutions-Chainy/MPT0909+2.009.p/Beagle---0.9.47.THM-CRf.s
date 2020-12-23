%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:57 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   41 (  46 expanded)
%              Number of leaves         :   22 (  27 expanded)
%              Depth                    :   10
%              Number of atoms          :   86 ( 136 expanded)
%              Number of equality atoms :   47 (  77 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(f_81,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( m1_subset_1(E,k3_zfmisc_1(A,B,C))
       => ( ! [F] :
              ( m1_subset_1(F,A)
             => ! [G] :
                  ( m1_subset_1(G,B)
                 => ! [H] :
                      ( m1_subset_1(H,C)
                     => ( E = k3_mcart_1(F,G,H)
                       => D = F ) ) ) )
         => ( A = k1_xboole_0
            | B = k1_xboole_0
            | C = k1_xboole_0
            | D = k5_mcart_1(A,B,C,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_mcart_1)).

tff(f_33,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k5_mcart_1(A,B,C,D),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_mcart_1)).

tff(f_37,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k6_mcart_1(A,B,C,D),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_mcart_1)).

tff(f_41,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k7_mcart_1(A,B,C,D),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_mcart_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => D = k3_mcart_1(k5_mcart_1(A,B,C,D),k6_mcart_1(A,B,C,D),k7_mcart_1(A,B,C,D)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).

tff(c_14,plain,(
    k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_24,plain,(
    m1_subset_1('#skF_5',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_6,plain,(
    ! [A_7,B_8,C_9,D_10] :
      ( m1_subset_1(k5_mcart_1(A_7,B_8,C_9,D_10),A_7)
      | ~ m1_subset_1(D_10,k3_zfmisc_1(A_7,B_8,C_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_8,plain,(
    ! [A_11,B_12,C_13,D_14] :
      ( m1_subset_1(k6_mcart_1(A_11,B_12,C_13,D_14),B_12)
      | ~ m1_subset_1(D_14,k3_zfmisc_1(A_11,B_12,C_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_10,plain,(
    ! [A_15,B_16,C_17,D_18] :
      ( m1_subset_1(k7_mcart_1(A_15,B_16,C_17,D_18),C_17)
      | ~ m1_subset_1(D_18,k3_zfmisc_1(A_15,B_16,C_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_95,plain,(
    ! [A_67,B_68,C_69,D_70] :
      ( k3_mcart_1(k5_mcart_1(A_67,B_68,C_69,D_70),k6_mcart_1(A_67,B_68,C_69,D_70),k7_mcart_1(A_67,B_68,C_69,D_70)) = D_70
      | ~ m1_subset_1(D_70,k3_zfmisc_1(A_67,B_68,C_69))
      | k1_xboole_0 = C_69
      | k1_xboole_0 = B_68
      | k1_xboole_0 = A_67 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_22,plain,(
    ! [F_31,G_35,H_37] :
      ( F_31 = '#skF_4'
      | k3_mcart_1(F_31,G_35,H_37) != '#skF_5'
      | ~ m1_subset_1(H_37,'#skF_3')
      | ~ m1_subset_1(G_35,'#skF_2')
      | ~ m1_subset_1(F_31,'#skF_1') ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_113,plain,(
    ! [A_75,B_76,C_77,D_78] :
      ( k5_mcart_1(A_75,B_76,C_77,D_78) = '#skF_4'
      | D_78 != '#skF_5'
      | ~ m1_subset_1(k7_mcart_1(A_75,B_76,C_77,D_78),'#skF_3')
      | ~ m1_subset_1(k6_mcart_1(A_75,B_76,C_77,D_78),'#skF_2')
      | ~ m1_subset_1(k5_mcart_1(A_75,B_76,C_77,D_78),'#skF_1')
      | ~ m1_subset_1(D_78,k3_zfmisc_1(A_75,B_76,C_77))
      | k1_xboole_0 = C_77
      | k1_xboole_0 = B_76
      | k1_xboole_0 = A_75 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_22])).

tff(c_117,plain,(
    ! [A_15,B_16,D_18] :
      ( k5_mcart_1(A_15,B_16,'#skF_3',D_18) = '#skF_4'
      | D_18 != '#skF_5'
      | ~ m1_subset_1(k6_mcart_1(A_15,B_16,'#skF_3',D_18),'#skF_2')
      | ~ m1_subset_1(k5_mcart_1(A_15,B_16,'#skF_3',D_18),'#skF_1')
      | k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = B_16
      | k1_xboole_0 = A_15
      | ~ m1_subset_1(D_18,k3_zfmisc_1(A_15,B_16,'#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_10,c_113])).

tff(c_122,plain,(
    ! [A_79,B_80,D_81] :
      ( k5_mcart_1(A_79,B_80,'#skF_3',D_81) = '#skF_4'
      | D_81 != '#skF_5'
      | ~ m1_subset_1(k6_mcart_1(A_79,B_80,'#skF_3',D_81),'#skF_2')
      | ~ m1_subset_1(k5_mcart_1(A_79,B_80,'#skF_3',D_81),'#skF_1')
      | k1_xboole_0 = B_80
      | k1_xboole_0 = A_79
      | ~ m1_subset_1(D_81,k3_zfmisc_1(A_79,B_80,'#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_117])).

tff(c_126,plain,(
    ! [A_11,D_14] :
      ( k5_mcart_1(A_11,'#skF_2','#skF_3',D_14) = '#skF_4'
      | D_14 != '#skF_5'
      | ~ m1_subset_1(k5_mcart_1(A_11,'#skF_2','#skF_3',D_14),'#skF_1')
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = A_11
      | ~ m1_subset_1(D_14,k3_zfmisc_1(A_11,'#skF_2','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_8,c_122])).

tff(c_131,plain,(
    ! [A_82,D_83] :
      ( k5_mcart_1(A_82,'#skF_2','#skF_3',D_83) = '#skF_4'
      | D_83 != '#skF_5'
      | ~ m1_subset_1(k5_mcart_1(A_82,'#skF_2','#skF_3',D_83),'#skF_1')
      | k1_xboole_0 = A_82
      | ~ m1_subset_1(D_83,k3_zfmisc_1(A_82,'#skF_2','#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_126])).

tff(c_135,plain,(
    ! [D_10] :
      ( k5_mcart_1('#skF_1','#skF_2','#skF_3',D_10) = '#skF_4'
      | D_10 != '#skF_5'
      | k1_xboole_0 = '#skF_1'
      | ~ m1_subset_1(D_10,k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_6,c_131])).

tff(c_140,plain,(
    ! [D_84] :
      ( k5_mcart_1('#skF_1','#skF_2','#skF_3',D_84) = '#skF_4'
      | D_84 != '#skF_5'
      | ~ m1_subset_1(D_84,k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_135])).

tff(c_155,plain,(
    k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_24,c_140])).

tff(c_162,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_155])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:45:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.80/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.15  
% 1.80/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.15  %$ m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.80/1.15  
% 1.80/1.15  %Foreground sorts:
% 1.80/1.15  
% 1.80/1.15  
% 1.80/1.15  %Background operators:
% 1.80/1.15  
% 1.80/1.15  
% 1.80/1.15  %Foreground operators:
% 1.80/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.80/1.15  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.80/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.80/1.15  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 1.80/1.15  tff('#skF_5', type, '#skF_5': $i).
% 1.80/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.80/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.80/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.80/1.15  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 1.80/1.15  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 1.80/1.15  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 1.80/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.80/1.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.80/1.15  tff('#skF_4', type, '#skF_4': $i).
% 1.80/1.15  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 1.80/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.80/1.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.80/1.15  
% 1.80/1.16  tff(f_81, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k3_zfmisc_1(A, B, C)) => ((![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => ((E = k3_mcart_1(F, G, H)) => (D = F)))))))) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k5_mcart_1(A, B, C, E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_mcart_1)).
% 1.80/1.16  tff(f_33, axiom, (![A, B, C, D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => m1_subset_1(k5_mcart_1(A, B, C, D), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_mcart_1)).
% 1.80/1.16  tff(f_37, axiom, (![A, B, C, D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => m1_subset_1(k6_mcart_1(A, B, C, D), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_mcart_1)).
% 1.80/1.16  tff(f_41, axiom, (![A, B, C, D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => m1_subset_1(k7_mcart_1(A, B, C, D), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_mcart_1)).
% 1.80/1.16  tff(f_57, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (D = k3_mcart_1(k5_mcart_1(A, B, C, D), k6_mcart_1(A, B, C, D), k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_mcart_1)).
% 1.80/1.16  tff(c_14, plain, (k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.80/1.16  tff(c_24, plain, (m1_subset_1('#skF_5', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.80/1.16  tff(c_20, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.80/1.16  tff(c_6, plain, (![A_7, B_8, C_9, D_10]: (m1_subset_1(k5_mcart_1(A_7, B_8, C_9, D_10), A_7) | ~m1_subset_1(D_10, k3_zfmisc_1(A_7, B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.80/1.16  tff(c_18, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.80/1.16  tff(c_8, plain, (![A_11, B_12, C_13, D_14]: (m1_subset_1(k6_mcart_1(A_11, B_12, C_13, D_14), B_12) | ~m1_subset_1(D_14, k3_zfmisc_1(A_11, B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.80/1.16  tff(c_16, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.80/1.16  tff(c_10, plain, (![A_15, B_16, C_17, D_18]: (m1_subset_1(k7_mcart_1(A_15, B_16, C_17, D_18), C_17) | ~m1_subset_1(D_18, k3_zfmisc_1(A_15, B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.80/1.16  tff(c_95, plain, (![A_67, B_68, C_69, D_70]: (k3_mcart_1(k5_mcart_1(A_67, B_68, C_69, D_70), k6_mcart_1(A_67, B_68, C_69, D_70), k7_mcart_1(A_67, B_68, C_69, D_70))=D_70 | ~m1_subset_1(D_70, k3_zfmisc_1(A_67, B_68, C_69)) | k1_xboole_0=C_69 | k1_xboole_0=B_68 | k1_xboole_0=A_67)), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.80/1.16  tff(c_22, plain, (![F_31, G_35, H_37]: (F_31='#skF_4' | k3_mcart_1(F_31, G_35, H_37)!='#skF_5' | ~m1_subset_1(H_37, '#skF_3') | ~m1_subset_1(G_35, '#skF_2') | ~m1_subset_1(F_31, '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.80/1.16  tff(c_113, plain, (![A_75, B_76, C_77, D_78]: (k5_mcart_1(A_75, B_76, C_77, D_78)='#skF_4' | D_78!='#skF_5' | ~m1_subset_1(k7_mcart_1(A_75, B_76, C_77, D_78), '#skF_3') | ~m1_subset_1(k6_mcart_1(A_75, B_76, C_77, D_78), '#skF_2') | ~m1_subset_1(k5_mcart_1(A_75, B_76, C_77, D_78), '#skF_1') | ~m1_subset_1(D_78, k3_zfmisc_1(A_75, B_76, C_77)) | k1_xboole_0=C_77 | k1_xboole_0=B_76 | k1_xboole_0=A_75)), inference(superposition, [status(thm), theory('equality')], [c_95, c_22])).
% 1.80/1.16  tff(c_117, plain, (![A_15, B_16, D_18]: (k5_mcart_1(A_15, B_16, '#skF_3', D_18)='#skF_4' | D_18!='#skF_5' | ~m1_subset_1(k6_mcart_1(A_15, B_16, '#skF_3', D_18), '#skF_2') | ~m1_subset_1(k5_mcart_1(A_15, B_16, '#skF_3', D_18), '#skF_1') | k1_xboole_0='#skF_3' | k1_xboole_0=B_16 | k1_xboole_0=A_15 | ~m1_subset_1(D_18, k3_zfmisc_1(A_15, B_16, '#skF_3')))), inference(resolution, [status(thm)], [c_10, c_113])).
% 1.80/1.16  tff(c_122, plain, (![A_79, B_80, D_81]: (k5_mcart_1(A_79, B_80, '#skF_3', D_81)='#skF_4' | D_81!='#skF_5' | ~m1_subset_1(k6_mcart_1(A_79, B_80, '#skF_3', D_81), '#skF_2') | ~m1_subset_1(k5_mcart_1(A_79, B_80, '#skF_3', D_81), '#skF_1') | k1_xboole_0=B_80 | k1_xboole_0=A_79 | ~m1_subset_1(D_81, k3_zfmisc_1(A_79, B_80, '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_16, c_117])).
% 1.80/1.16  tff(c_126, plain, (![A_11, D_14]: (k5_mcart_1(A_11, '#skF_2', '#skF_3', D_14)='#skF_4' | D_14!='#skF_5' | ~m1_subset_1(k5_mcart_1(A_11, '#skF_2', '#skF_3', D_14), '#skF_1') | k1_xboole_0='#skF_2' | k1_xboole_0=A_11 | ~m1_subset_1(D_14, k3_zfmisc_1(A_11, '#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_8, c_122])).
% 1.80/1.16  tff(c_131, plain, (![A_82, D_83]: (k5_mcart_1(A_82, '#skF_2', '#skF_3', D_83)='#skF_4' | D_83!='#skF_5' | ~m1_subset_1(k5_mcart_1(A_82, '#skF_2', '#skF_3', D_83), '#skF_1') | k1_xboole_0=A_82 | ~m1_subset_1(D_83, k3_zfmisc_1(A_82, '#skF_2', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_18, c_126])).
% 1.80/1.16  tff(c_135, plain, (![D_10]: (k5_mcart_1('#skF_1', '#skF_2', '#skF_3', D_10)='#skF_4' | D_10!='#skF_5' | k1_xboole_0='#skF_1' | ~m1_subset_1(D_10, k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_6, c_131])).
% 1.80/1.16  tff(c_140, plain, (![D_84]: (k5_mcart_1('#skF_1', '#skF_2', '#skF_3', D_84)='#skF_4' | D_84!='#skF_5' | ~m1_subset_1(D_84, k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_20, c_135])).
% 1.80/1.16  tff(c_155, plain, (k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_24, c_140])).
% 1.80/1.16  tff(c_162, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_155])).
% 1.80/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.16  
% 1.80/1.16  Inference rules
% 1.80/1.16  ----------------------
% 1.80/1.16  #Ref     : 0
% 1.80/1.16  #Sup     : 27
% 1.80/1.16  #Fact    : 0
% 1.80/1.16  #Define  : 0
% 1.80/1.16  #Split   : 0
% 1.80/1.16  #Chain   : 0
% 1.80/1.16  #Close   : 0
% 1.80/1.16  
% 1.80/1.16  Ordering : KBO
% 1.80/1.16  
% 1.80/1.16  Simplification rules
% 1.80/1.16  ----------------------
% 1.80/1.16  #Subsume      : 1
% 1.80/1.16  #Demod        : 9
% 1.80/1.16  #Tautology    : 14
% 1.80/1.16  #SimpNegUnit  : 4
% 1.80/1.16  #BackRed      : 0
% 1.80/1.16  
% 1.80/1.16  #Partial instantiations: 0
% 1.80/1.16  #Strategies tried      : 1
% 1.80/1.16  
% 1.80/1.16  Timing (in seconds)
% 1.80/1.16  ----------------------
% 1.80/1.16  Preprocessing        : 0.28
% 1.80/1.16  Parsing              : 0.15
% 1.80/1.16  CNF conversion       : 0.02
% 1.80/1.16  Main loop            : 0.17
% 1.80/1.16  Inferencing          : 0.07
% 1.80/1.16  Reduction            : 0.05
% 1.80/1.16  Demodulation         : 0.04
% 1.80/1.16  BG Simplification    : 0.01
% 1.80/1.16  Subsumption          : 0.03
% 1.80/1.16  Abstraction          : 0.01
% 1.80/1.16  MUC search           : 0.00
% 1.80/1.16  Cooper               : 0.00
% 1.80/1.16  Total                : 0.48
% 1.80/1.16  Index Insertion      : 0.00
% 1.80/1.16  Index Deletion       : 0.00
% 1.80/1.16  Index Matching       : 0.00
% 1.80/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
