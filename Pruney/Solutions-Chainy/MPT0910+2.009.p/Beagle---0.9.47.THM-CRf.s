%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:00 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.00s
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
                       => D = G ) ) ) )
         => ( A = k1_xboole_0
            | B = k1_xboole_0
            | C = k1_xboole_0
            | D = k6_mcart_1(A,B,C,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_mcart_1)).

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
    k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') != '#skF_4' ),
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
    ! [G_35,F_31,H_37] :
      ( G_35 = '#skF_4'
      | k3_mcart_1(F_31,G_35,H_37) != '#skF_5'
      | ~ m1_subset_1(H_37,'#skF_3')
      | ~ m1_subset_1(G_35,'#skF_2')
      | ~ m1_subset_1(F_31,'#skF_1') ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_113,plain,(
    ! [A_75,B_76,C_77,D_78] :
      ( k6_mcart_1(A_75,B_76,C_77,D_78) = '#skF_4'
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
      ( k6_mcart_1(A_15,B_16,'#skF_3',D_18) = '#skF_4'
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
      ( k6_mcart_1(A_79,B_80,'#skF_3',D_81) = '#skF_4'
      | D_81 != '#skF_5'
      | ~ m1_subset_1(k6_mcart_1(A_79,B_80,'#skF_3',D_81),'#skF_2')
      | ~ m1_subset_1(k5_mcart_1(A_79,B_80,'#skF_3',D_81),'#skF_1')
      | k1_xboole_0 = B_80
      | k1_xboole_0 = A_79
      | ~ m1_subset_1(D_81,k3_zfmisc_1(A_79,B_80,'#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_117])).

tff(c_126,plain,(
    ! [A_11,D_14] :
      ( k6_mcart_1(A_11,'#skF_2','#skF_3',D_14) = '#skF_4'
      | D_14 != '#skF_5'
      | ~ m1_subset_1(k5_mcart_1(A_11,'#skF_2','#skF_3',D_14),'#skF_1')
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = A_11
      | ~ m1_subset_1(D_14,k3_zfmisc_1(A_11,'#skF_2','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_8,c_122])).

tff(c_131,plain,(
    ! [A_82,D_83] :
      ( k6_mcart_1(A_82,'#skF_2','#skF_3',D_83) = '#skF_4'
      | D_83 != '#skF_5'
      | ~ m1_subset_1(k5_mcart_1(A_82,'#skF_2','#skF_3',D_83),'#skF_1')
      | k1_xboole_0 = A_82
      | ~ m1_subset_1(D_83,k3_zfmisc_1(A_82,'#skF_2','#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_126])).

tff(c_135,plain,(
    ! [D_10] :
      ( k6_mcart_1('#skF_1','#skF_2','#skF_3',D_10) = '#skF_4'
      | D_10 != '#skF_5'
      | k1_xboole_0 = '#skF_1'
      | ~ m1_subset_1(D_10,k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_6,c_131])).

tff(c_140,plain,(
    ! [D_84] :
      ( k6_mcart_1('#skF_1','#skF_2','#skF_3',D_84) = '#skF_4'
      | D_84 != '#skF_5'
      | ~ m1_subset_1(D_84,k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_135])).

tff(c_155,plain,(
    k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_24,c_140])).

tff(c_162,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_155])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:01:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.29  
% 2.00/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.30  %$ m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.00/1.30  
% 2.00/1.30  %Foreground sorts:
% 2.00/1.30  
% 2.00/1.30  
% 2.00/1.30  %Background operators:
% 2.00/1.30  
% 2.00/1.30  
% 2.00/1.30  %Foreground operators:
% 2.00/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.30  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.00/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.00/1.30  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.00/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.00/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.00/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.00/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.00/1.30  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 2.00/1.30  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.00/1.30  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 2.00/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.00/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.00/1.30  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 2.00/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.00/1.30  
% 2.00/1.31  tff(f_81, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k3_zfmisc_1(A, B, C)) => ((![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => ((E = k3_mcart_1(F, G, H)) => (D = G)))))))) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k6_mcart_1(A, B, C, E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_mcart_1)).
% 2.00/1.31  tff(f_33, axiom, (![A, B, C, D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => m1_subset_1(k5_mcart_1(A, B, C, D), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_mcart_1)).
% 2.00/1.31  tff(f_37, axiom, (![A, B, C, D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => m1_subset_1(k6_mcart_1(A, B, C, D), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_mcart_1)).
% 2.00/1.31  tff(f_41, axiom, (![A, B, C, D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => m1_subset_1(k7_mcart_1(A, B, C, D), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_mcart_1)).
% 2.00/1.31  tff(f_57, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (D = k3_mcart_1(k5_mcart_1(A, B, C, D), k6_mcart_1(A, B, C, D), k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_mcart_1)).
% 2.00/1.31  tff(c_14, plain, (k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.00/1.31  tff(c_24, plain, (m1_subset_1('#skF_5', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.00/1.31  tff(c_20, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.00/1.31  tff(c_6, plain, (![A_7, B_8, C_9, D_10]: (m1_subset_1(k5_mcart_1(A_7, B_8, C_9, D_10), A_7) | ~m1_subset_1(D_10, k3_zfmisc_1(A_7, B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.00/1.31  tff(c_18, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.00/1.31  tff(c_8, plain, (![A_11, B_12, C_13, D_14]: (m1_subset_1(k6_mcart_1(A_11, B_12, C_13, D_14), B_12) | ~m1_subset_1(D_14, k3_zfmisc_1(A_11, B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.00/1.31  tff(c_16, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.00/1.31  tff(c_10, plain, (![A_15, B_16, C_17, D_18]: (m1_subset_1(k7_mcart_1(A_15, B_16, C_17, D_18), C_17) | ~m1_subset_1(D_18, k3_zfmisc_1(A_15, B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.00/1.31  tff(c_95, plain, (![A_67, B_68, C_69, D_70]: (k3_mcart_1(k5_mcart_1(A_67, B_68, C_69, D_70), k6_mcart_1(A_67, B_68, C_69, D_70), k7_mcart_1(A_67, B_68, C_69, D_70))=D_70 | ~m1_subset_1(D_70, k3_zfmisc_1(A_67, B_68, C_69)) | k1_xboole_0=C_69 | k1_xboole_0=B_68 | k1_xboole_0=A_67)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.00/1.31  tff(c_22, plain, (![G_35, F_31, H_37]: (G_35='#skF_4' | k3_mcart_1(F_31, G_35, H_37)!='#skF_5' | ~m1_subset_1(H_37, '#skF_3') | ~m1_subset_1(G_35, '#skF_2') | ~m1_subset_1(F_31, '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.00/1.31  tff(c_113, plain, (![A_75, B_76, C_77, D_78]: (k6_mcart_1(A_75, B_76, C_77, D_78)='#skF_4' | D_78!='#skF_5' | ~m1_subset_1(k7_mcart_1(A_75, B_76, C_77, D_78), '#skF_3') | ~m1_subset_1(k6_mcart_1(A_75, B_76, C_77, D_78), '#skF_2') | ~m1_subset_1(k5_mcart_1(A_75, B_76, C_77, D_78), '#skF_1') | ~m1_subset_1(D_78, k3_zfmisc_1(A_75, B_76, C_77)) | k1_xboole_0=C_77 | k1_xboole_0=B_76 | k1_xboole_0=A_75)), inference(superposition, [status(thm), theory('equality')], [c_95, c_22])).
% 2.00/1.31  tff(c_117, plain, (![A_15, B_16, D_18]: (k6_mcart_1(A_15, B_16, '#skF_3', D_18)='#skF_4' | D_18!='#skF_5' | ~m1_subset_1(k6_mcart_1(A_15, B_16, '#skF_3', D_18), '#skF_2') | ~m1_subset_1(k5_mcart_1(A_15, B_16, '#skF_3', D_18), '#skF_1') | k1_xboole_0='#skF_3' | k1_xboole_0=B_16 | k1_xboole_0=A_15 | ~m1_subset_1(D_18, k3_zfmisc_1(A_15, B_16, '#skF_3')))), inference(resolution, [status(thm)], [c_10, c_113])).
% 2.00/1.31  tff(c_122, plain, (![A_79, B_80, D_81]: (k6_mcart_1(A_79, B_80, '#skF_3', D_81)='#skF_4' | D_81!='#skF_5' | ~m1_subset_1(k6_mcart_1(A_79, B_80, '#skF_3', D_81), '#skF_2') | ~m1_subset_1(k5_mcart_1(A_79, B_80, '#skF_3', D_81), '#skF_1') | k1_xboole_0=B_80 | k1_xboole_0=A_79 | ~m1_subset_1(D_81, k3_zfmisc_1(A_79, B_80, '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_16, c_117])).
% 2.00/1.31  tff(c_126, plain, (![A_11, D_14]: (k6_mcart_1(A_11, '#skF_2', '#skF_3', D_14)='#skF_4' | D_14!='#skF_5' | ~m1_subset_1(k5_mcart_1(A_11, '#skF_2', '#skF_3', D_14), '#skF_1') | k1_xboole_0='#skF_2' | k1_xboole_0=A_11 | ~m1_subset_1(D_14, k3_zfmisc_1(A_11, '#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_8, c_122])).
% 2.00/1.31  tff(c_131, plain, (![A_82, D_83]: (k6_mcart_1(A_82, '#skF_2', '#skF_3', D_83)='#skF_4' | D_83!='#skF_5' | ~m1_subset_1(k5_mcart_1(A_82, '#skF_2', '#skF_3', D_83), '#skF_1') | k1_xboole_0=A_82 | ~m1_subset_1(D_83, k3_zfmisc_1(A_82, '#skF_2', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_18, c_126])).
% 2.00/1.31  tff(c_135, plain, (![D_10]: (k6_mcart_1('#skF_1', '#skF_2', '#skF_3', D_10)='#skF_4' | D_10!='#skF_5' | k1_xboole_0='#skF_1' | ~m1_subset_1(D_10, k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_6, c_131])).
% 2.00/1.31  tff(c_140, plain, (![D_84]: (k6_mcart_1('#skF_1', '#skF_2', '#skF_3', D_84)='#skF_4' | D_84!='#skF_5' | ~m1_subset_1(D_84, k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_20, c_135])).
% 2.00/1.31  tff(c_155, plain, (k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_24, c_140])).
% 2.00/1.31  tff(c_162, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_155])).
% 2.00/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.31  
% 2.00/1.31  Inference rules
% 2.00/1.31  ----------------------
% 2.00/1.31  #Ref     : 0
% 2.00/1.31  #Sup     : 27
% 2.00/1.31  #Fact    : 0
% 2.00/1.31  #Define  : 0
% 2.00/1.31  #Split   : 0
% 2.00/1.31  #Chain   : 0
% 2.00/1.31  #Close   : 0
% 2.00/1.31  
% 2.00/1.31  Ordering : KBO
% 2.00/1.31  
% 2.00/1.31  Simplification rules
% 2.00/1.31  ----------------------
% 2.00/1.31  #Subsume      : 1
% 2.00/1.31  #Demod        : 8
% 2.00/1.31  #Tautology    : 14
% 2.00/1.31  #SimpNegUnit  : 4
% 2.00/1.31  #BackRed      : 0
% 2.00/1.31  
% 2.00/1.31  #Partial instantiations: 0
% 2.00/1.31  #Strategies tried      : 1
% 2.00/1.31  
% 2.00/1.31  Timing (in seconds)
% 2.00/1.31  ----------------------
% 2.00/1.31  Preprocessing        : 0.29
% 2.00/1.31  Parsing              : 0.16
% 2.00/1.32  CNF conversion       : 0.02
% 2.00/1.32  Main loop            : 0.19
% 2.00/1.32  Inferencing          : 0.08
% 2.00/1.32  Reduction            : 0.05
% 2.00/1.32  Demodulation         : 0.04
% 2.00/1.32  BG Simplification    : 0.01
% 2.00/1.32  Subsumption          : 0.03
% 2.00/1.32  Abstraction          : 0.01
% 2.00/1.32  MUC search           : 0.00
% 2.00/1.32  Cooper               : 0.00
% 2.00/1.32  Total                : 0.51
% 2.00/1.32  Index Insertion      : 0.00
% 2.00/1.32  Index Deletion       : 0.00
% 2.00/1.32  Index Matching       : 0.00
% 2.00/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
