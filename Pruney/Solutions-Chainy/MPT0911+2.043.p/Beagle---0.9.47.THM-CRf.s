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
% DateTime   : Thu Dec  3 10:10:07 EST 2020

% Result     : Theorem 1.75s
% Output     : CNFRefutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :   39 (  44 expanded)
%              Number of leaves         :   20 (  25 expanded)
%              Depth                    :   10
%              Number of atoms          :   86 ( 136 expanded)
%              Number of equality atoms :   47 (  77 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( m1_subset_1(E,k3_zfmisc_1(A,B,C))
       => ( ! [F] :
              ( m1_subset_1(F,A)
             => ! [G] :
                  ( m1_subset_1(G,B)
                 => ! [H] :
                      ( m1_subset_1(H,C)
                     => ( E = k3_mcart_1(F,G,H)
                       => D = H ) ) ) )
         => ( A = k1_xboole_0
            | B = k1_xboole_0
            | C = k1_xboole_0
            | D = k7_mcart_1(A,B,C,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_mcart_1)).

tff(f_29,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k5_mcart_1(A,B,C,D),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_mcart_1)).

tff(f_33,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k6_mcart_1(A,B,C,D),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_mcart_1)).

tff(f_37,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k7_mcart_1(A,B,C,D),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_mcart_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => D = k3_mcart_1(k5_mcart_1(A,B,C,D),k6_mcart_1(A,B,C,D),k7_mcart_1(A,B,C,D)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).

tff(c_10,plain,(
    k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_20,plain,(
    m1_subset_1('#skF_5',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_16,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3,D_4] :
      ( m1_subset_1(k5_mcart_1(A_1,B_2,C_3,D_4),A_1)
      | ~ m1_subset_1(D_4,k3_zfmisc_1(A_1,B_2,C_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_4,plain,(
    ! [A_5,B_6,C_7,D_8] :
      ( m1_subset_1(k6_mcart_1(A_5,B_6,C_7,D_8),B_6)
      | ~ m1_subset_1(D_8,k3_zfmisc_1(A_5,B_6,C_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_6,plain,(
    ! [A_9,B_10,C_11,D_12] :
      ( m1_subset_1(k7_mcart_1(A_9,B_10,C_11,D_12),C_11)
      | ~ m1_subset_1(D_12,k3_zfmisc_1(A_9,B_10,C_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_31,plain,(
    ! [A_47,B_48,C_49,D_50] :
      ( k3_mcart_1(k5_mcart_1(A_47,B_48,C_49,D_50),k6_mcart_1(A_47,B_48,C_49,D_50),k7_mcart_1(A_47,B_48,C_49,D_50)) = D_50
      | ~ m1_subset_1(D_50,k3_zfmisc_1(A_47,B_48,C_49))
      | k1_xboole_0 = C_49
      | k1_xboole_0 = B_48
      | k1_xboole_0 = A_47 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_18,plain,(
    ! [H_31,F_25,G_29] :
      ( H_31 = '#skF_4'
      | k3_mcart_1(F_25,G_29,H_31) != '#skF_5'
      | ~ m1_subset_1(H_31,'#skF_3')
      | ~ m1_subset_1(G_29,'#skF_2')
      | ~ m1_subset_1(F_25,'#skF_1') ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_43,plain,(
    ! [A_51,B_52,C_53,D_54] :
      ( k7_mcart_1(A_51,B_52,C_53,D_54) = '#skF_4'
      | D_54 != '#skF_5'
      | ~ m1_subset_1(k7_mcart_1(A_51,B_52,C_53,D_54),'#skF_3')
      | ~ m1_subset_1(k6_mcart_1(A_51,B_52,C_53,D_54),'#skF_2')
      | ~ m1_subset_1(k5_mcart_1(A_51,B_52,C_53,D_54),'#skF_1')
      | ~ m1_subset_1(D_54,k3_zfmisc_1(A_51,B_52,C_53))
      | k1_xboole_0 = C_53
      | k1_xboole_0 = B_52
      | k1_xboole_0 = A_51 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31,c_18])).

tff(c_47,plain,(
    ! [A_9,B_10,D_12] :
      ( k7_mcart_1(A_9,B_10,'#skF_3',D_12) = '#skF_4'
      | D_12 != '#skF_5'
      | ~ m1_subset_1(k6_mcart_1(A_9,B_10,'#skF_3',D_12),'#skF_2')
      | ~ m1_subset_1(k5_mcart_1(A_9,B_10,'#skF_3',D_12),'#skF_1')
      | k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = B_10
      | k1_xboole_0 = A_9
      | ~ m1_subset_1(D_12,k3_zfmisc_1(A_9,B_10,'#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_6,c_43])).

tff(c_52,plain,(
    ! [A_55,B_56,D_57] :
      ( k7_mcart_1(A_55,B_56,'#skF_3',D_57) = '#skF_4'
      | D_57 != '#skF_5'
      | ~ m1_subset_1(k6_mcart_1(A_55,B_56,'#skF_3',D_57),'#skF_2')
      | ~ m1_subset_1(k5_mcart_1(A_55,B_56,'#skF_3',D_57),'#skF_1')
      | k1_xboole_0 = B_56
      | k1_xboole_0 = A_55
      | ~ m1_subset_1(D_57,k3_zfmisc_1(A_55,B_56,'#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_47])).

tff(c_56,plain,(
    ! [A_5,D_8] :
      ( k7_mcart_1(A_5,'#skF_2','#skF_3',D_8) = '#skF_4'
      | D_8 != '#skF_5'
      | ~ m1_subset_1(k5_mcart_1(A_5,'#skF_2','#skF_3',D_8),'#skF_1')
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = A_5
      | ~ m1_subset_1(D_8,k3_zfmisc_1(A_5,'#skF_2','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_4,c_52])).

tff(c_61,plain,(
    ! [A_58,D_59] :
      ( k7_mcart_1(A_58,'#skF_2','#skF_3',D_59) = '#skF_4'
      | D_59 != '#skF_5'
      | ~ m1_subset_1(k5_mcart_1(A_58,'#skF_2','#skF_3',D_59),'#skF_1')
      | k1_xboole_0 = A_58
      | ~ m1_subset_1(D_59,k3_zfmisc_1(A_58,'#skF_2','#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_56])).

tff(c_65,plain,(
    ! [D_4] :
      ( k7_mcart_1('#skF_1','#skF_2','#skF_3',D_4) = '#skF_4'
      | D_4 != '#skF_5'
      | k1_xboole_0 = '#skF_1'
      | ~ m1_subset_1(D_4,k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_2,c_61])).

tff(c_70,plain,(
    ! [D_60] :
      ( k7_mcart_1('#skF_1','#skF_2','#skF_3',D_60) = '#skF_4'
      | D_60 != '#skF_5'
      | ~ m1_subset_1(D_60,k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_65])).

tff(c_85,plain,(
    k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_20,c_70])).

tff(c_92,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_85])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:49:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.75/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.22  
% 1.75/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.22  %$ m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.75/1.22  
% 1.75/1.22  %Foreground sorts:
% 1.75/1.22  
% 1.75/1.22  
% 1.75/1.22  %Background operators:
% 1.75/1.22  
% 1.75/1.22  
% 1.75/1.22  %Foreground operators:
% 1.75/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.75/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.75/1.22  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 1.75/1.22  tff('#skF_5', type, '#skF_5': $i).
% 1.75/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.75/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.75/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.75/1.22  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 1.75/1.22  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 1.75/1.22  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 1.75/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.75/1.22  tff('#skF_4', type, '#skF_4': $i).
% 1.75/1.22  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 1.75/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.75/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.75/1.22  
% 1.75/1.23  tff(f_77, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k3_zfmisc_1(A, B, C)) => ((![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => ((E = k3_mcart_1(F, G, H)) => (D = H)))))))) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k7_mcart_1(A, B, C, E)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_mcart_1)).
% 1.75/1.23  tff(f_29, axiom, (![A, B, C, D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => m1_subset_1(k5_mcart_1(A, B, C, D), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_mcart_1)).
% 1.75/1.23  tff(f_33, axiom, (![A, B, C, D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => m1_subset_1(k6_mcart_1(A, B, C, D), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_mcart_1)).
% 1.75/1.23  tff(f_37, axiom, (![A, B, C, D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => m1_subset_1(k7_mcart_1(A, B, C, D), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_mcart_1)).
% 1.75/1.23  tff(f_53, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (D = k3_mcart_1(k5_mcart_1(A, B, C, D), k6_mcart_1(A, B, C, D), k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_mcart_1)).
% 1.75/1.23  tff(c_10, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_77])).
% 1.75/1.23  tff(c_20, plain, (m1_subset_1('#skF_5', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 1.75/1.23  tff(c_16, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_77])).
% 1.75/1.23  tff(c_2, plain, (![A_1, B_2, C_3, D_4]: (m1_subset_1(k5_mcart_1(A_1, B_2, C_3, D_4), A_1) | ~m1_subset_1(D_4, k3_zfmisc_1(A_1, B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.75/1.23  tff(c_14, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_77])).
% 1.75/1.23  tff(c_4, plain, (![A_5, B_6, C_7, D_8]: (m1_subset_1(k6_mcart_1(A_5, B_6, C_7, D_8), B_6) | ~m1_subset_1(D_8, k3_zfmisc_1(A_5, B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.75/1.23  tff(c_12, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_77])).
% 1.75/1.23  tff(c_6, plain, (![A_9, B_10, C_11, D_12]: (m1_subset_1(k7_mcart_1(A_9, B_10, C_11, D_12), C_11) | ~m1_subset_1(D_12, k3_zfmisc_1(A_9, B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.75/1.23  tff(c_31, plain, (![A_47, B_48, C_49, D_50]: (k3_mcart_1(k5_mcart_1(A_47, B_48, C_49, D_50), k6_mcart_1(A_47, B_48, C_49, D_50), k7_mcart_1(A_47, B_48, C_49, D_50))=D_50 | ~m1_subset_1(D_50, k3_zfmisc_1(A_47, B_48, C_49)) | k1_xboole_0=C_49 | k1_xboole_0=B_48 | k1_xboole_0=A_47)), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.75/1.23  tff(c_18, plain, (![H_31, F_25, G_29]: (H_31='#skF_4' | k3_mcart_1(F_25, G_29, H_31)!='#skF_5' | ~m1_subset_1(H_31, '#skF_3') | ~m1_subset_1(G_29, '#skF_2') | ~m1_subset_1(F_25, '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 1.75/1.23  tff(c_43, plain, (![A_51, B_52, C_53, D_54]: (k7_mcart_1(A_51, B_52, C_53, D_54)='#skF_4' | D_54!='#skF_5' | ~m1_subset_1(k7_mcart_1(A_51, B_52, C_53, D_54), '#skF_3') | ~m1_subset_1(k6_mcart_1(A_51, B_52, C_53, D_54), '#skF_2') | ~m1_subset_1(k5_mcart_1(A_51, B_52, C_53, D_54), '#skF_1') | ~m1_subset_1(D_54, k3_zfmisc_1(A_51, B_52, C_53)) | k1_xboole_0=C_53 | k1_xboole_0=B_52 | k1_xboole_0=A_51)), inference(superposition, [status(thm), theory('equality')], [c_31, c_18])).
% 1.75/1.23  tff(c_47, plain, (![A_9, B_10, D_12]: (k7_mcart_1(A_9, B_10, '#skF_3', D_12)='#skF_4' | D_12!='#skF_5' | ~m1_subset_1(k6_mcart_1(A_9, B_10, '#skF_3', D_12), '#skF_2') | ~m1_subset_1(k5_mcart_1(A_9, B_10, '#skF_3', D_12), '#skF_1') | k1_xboole_0='#skF_3' | k1_xboole_0=B_10 | k1_xboole_0=A_9 | ~m1_subset_1(D_12, k3_zfmisc_1(A_9, B_10, '#skF_3')))), inference(resolution, [status(thm)], [c_6, c_43])).
% 1.75/1.23  tff(c_52, plain, (![A_55, B_56, D_57]: (k7_mcart_1(A_55, B_56, '#skF_3', D_57)='#skF_4' | D_57!='#skF_5' | ~m1_subset_1(k6_mcart_1(A_55, B_56, '#skF_3', D_57), '#skF_2') | ~m1_subset_1(k5_mcart_1(A_55, B_56, '#skF_3', D_57), '#skF_1') | k1_xboole_0=B_56 | k1_xboole_0=A_55 | ~m1_subset_1(D_57, k3_zfmisc_1(A_55, B_56, '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_12, c_47])).
% 1.75/1.23  tff(c_56, plain, (![A_5, D_8]: (k7_mcart_1(A_5, '#skF_2', '#skF_3', D_8)='#skF_4' | D_8!='#skF_5' | ~m1_subset_1(k5_mcart_1(A_5, '#skF_2', '#skF_3', D_8), '#skF_1') | k1_xboole_0='#skF_2' | k1_xboole_0=A_5 | ~m1_subset_1(D_8, k3_zfmisc_1(A_5, '#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_4, c_52])).
% 1.75/1.23  tff(c_61, plain, (![A_58, D_59]: (k7_mcart_1(A_58, '#skF_2', '#skF_3', D_59)='#skF_4' | D_59!='#skF_5' | ~m1_subset_1(k5_mcart_1(A_58, '#skF_2', '#skF_3', D_59), '#skF_1') | k1_xboole_0=A_58 | ~m1_subset_1(D_59, k3_zfmisc_1(A_58, '#skF_2', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_14, c_56])).
% 1.75/1.23  tff(c_65, plain, (![D_4]: (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', D_4)='#skF_4' | D_4!='#skF_5' | k1_xboole_0='#skF_1' | ~m1_subset_1(D_4, k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_2, c_61])).
% 1.75/1.23  tff(c_70, plain, (![D_60]: (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', D_60)='#skF_4' | D_60!='#skF_5' | ~m1_subset_1(D_60, k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_16, c_65])).
% 1.75/1.23  tff(c_85, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_20, c_70])).
% 1.75/1.23  tff(c_92, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_85])).
% 1.75/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.75/1.23  
% 1.75/1.23  Inference rules
% 1.75/1.23  ----------------------
% 1.75/1.23  #Ref     : 0
% 1.75/1.23  #Sup     : 10
% 1.75/1.23  #Fact    : 0
% 1.75/1.23  #Define  : 0
% 1.75/1.23  #Split   : 0
% 1.75/1.23  #Chain   : 0
% 1.75/1.23  #Close   : 0
% 1.75/1.23  
% 1.75/1.23  Ordering : KBO
% 1.75/1.23  
% 1.75/1.23  Simplification rules
% 1.75/1.23  ----------------------
% 1.75/1.23  #Subsume      : 0
% 1.75/1.23  #Demod        : 0
% 1.75/1.23  #Tautology    : 2
% 1.75/1.23  #SimpNegUnit  : 4
% 1.75/1.23  #BackRed      : 0
% 1.75/1.23  
% 1.75/1.23  #Partial instantiations: 0
% 1.75/1.23  #Strategies tried      : 1
% 1.75/1.23  
% 1.75/1.23  Timing (in seconds)
% 1.75/1.23  ----------------------
% 1.75/1.23  Preprocessing        : 0.28
% 1.75/1.23  Parsing              : 0.15
% 1.75/1.24  CNF conversion       : 0.02
% 1.75/1.24  Main loop            : 0.13
% 1.75/1.24  Inferencing          : 0.06
% 1.75/1.24  Reduction            : 0.03
% 1.75/1.24  Demodulation         : 0.02
% 1.75/1.24  BG Simplification    : 0.01
% 1.75/1.24  Subsumption          : 0.03
% 1.75/1.24  Abstraction          : 0.01
% 1.75/1.24  MUC search           : 0.00
% 1.75/1.24  Cooper               : 0.00
% 1.75/1.24  Total                : 0.43
% 1.75/1.24  Index Insertion      : 0.00
% 1.75/1.24  Index Deletion       : 0.00
% 1.75/1.24  Index Matching       : 0.00
% 1.75/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
