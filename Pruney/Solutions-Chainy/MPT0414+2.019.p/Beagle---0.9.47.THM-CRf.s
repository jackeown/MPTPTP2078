%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:45 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 134 expanded)
%              Number of leaves         :   13 (  48 expanded)
%              Depth                    :   14
%              Number of atoms          :  103 ( 557 expanded)
%              Number of equality atoms :   23 ( 104 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k4_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_59,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(A))
                 => ( r2_hidden(D,B)
                  <=> r2_hidden(D,C) ) )
             => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_setfam_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ! [D] :
              ( m1_subset_1(D,k1_zfmisc_1(A))
             => ( ! [E] :
                    ( m1_subset_1(E,A)
                   => ( r2_hidden(E,B)
                    <=> ( r2_hidden(E,C)
                        | r2_hidden(E,D) ) ) )
               => B = k4_subset_1(A,C,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_subset_1)).

tff(c_16,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_18,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_14,plain,(
    ! [A_1,B_2,C_10,D_14] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_10,D_14),B_2)
      | r2_hidden('#skF_1'(A_1,B_2,C_10,D_14),D_14)
      | r2_hidden('#skF_1'(A_1,B_2,C_10,D_14),C_10)
      | k4_subset_1(A_1,C_10,D_14) = B_2
      | ~ m1_subset_1(D_14,k1_zfmisc_1(A_1))
      | ~ m1_subset_1(C_10,k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_110,plain,(
    ! [A_1,B_2,D_14] :
      ( r2_hidden('#skF_1'(A_1,B_2,D_14,D_14),B_2)
      | k4_subset_1(A_1,D_14,D_14) = B_2
      | ~ m1_subset_1(D_14,k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1))
      | r2_hidden('#skF_1'(A_1,B_2,D_14,D_14),D_14) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_14])).

tff(c_180,plain,(
    ! [A_1,B_2] :
      ( k4_subset_1(A_1,B_2,B_2) = B_2
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1))
      | r2_hidden('#skF_1'(A_1,B_2,B_2,B_2),B_2) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_110])).

tff(c_219,plain,(
    ! [A_54,B_55] :
      ( k4_subset_1(A_54,B_55,B_55) = B_55
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_54))
      | r2_hidden('#skF_1'(A_54,B_55,B_55,B_55),B_55) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_110])).

tff(c_4,plain,(
    ! [A_1,B_2,C_10,D_14] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_10,D_14),D_14)
      | ~ r2_hidden('#skF_1'(A_1,B_2,C_10,D_14),B_2)
      | k4_subset_1(A_1,C_10,D_14) = B_2
      | ~ m1_subset_1(D_14,k1_zfmisc_1(A_1))
      | ~ m1_subset_1(C_10,k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_490,plain,(
    ! [A_67,B_68] :
      ( ~ r2_hidden('#skF_1'(A_67,B_68,B_68,B_68),B_68)
      | k4_subset_1(A_67,B_68,B_68) = B_68
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_67)) ) ),
    inference(resolution,[status(thm)],[c_219,c_4])).

tff(c_516,plain,(
    ! [A_69,B_70] :
      ( k4_subset_1(A_69,B_70,B_70) = B_70
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_69)) ) ),
    inference(resolution,[status(thm)],[c_180,c_490])).

tff(c_525,plain,(
    k4_subset_1(k1_zfmisc_1('#skF_2'),'#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_18,c_516])).

tff(c_182,plain,(
    ! [A_51,B_52,D_53] :
      ( r2_hidden('#skF_1'(A_51,B_52,D_53,D_53),B_52)
      | k4_subset_1(A_51,D_53,D_53) = B_52
      | ~ m1_subset_1(D_53,k1_zfmisc_1(A_51))
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_51))
      | r2_hidden('#skF_1'(A_51,B_52,D_53,D_53),D_53) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_14])).

tff(c_27,plain,(
    ! [A_23,B_24,C_25,D_26] :
      ( m1_subset_1('#skF_1'(A_23,B_24,C_25,D_26),A_23)
      | k4_subset_1(A_23,C_25,D_26) = B_24
      | ~ m1_subset_1(D_26,k1_zfmisc_1(A_23))
      | ~ m1_subset_1(C_25,k1_zfmisc_1(A_23))
      | ~ m1_subset_1(B_24,k1_zfmisc_1(A_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_24,plain,(
    ! [D_20] :
      ( r2_hidden(D_20,'#skF_4')
      | ~ r2_hidden(D_20,'#skF_3')
      | ~ m1_subset_1(D_20,k1_zfmisc_1('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_36,plain,(
    ! [B_24,C_25,D_26] :
      ( r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'),B_24,C_25,D_26),'#skF_4')
      | ~ r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'),B_24,C_25,D_26),'#skF_3')
      | k4_subset_1(k1_zfmisc_1('#skF_2'),C_25,D_26) = B_24
      | ~ m1_subset_1(D_26,k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
      | ~ m1_subset_1(B_24,k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_27,c_24])).

tff(c_192,plain,(
    ! [D_53] :
      ( r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'),'#skF_3',D_53,D_53),'#skF_4')
      | k4_subset_1(k1_zfmisc_1('#skF_2'),D_53,D_53) = '#skF_3'
      | ~ m1_subset_1(D_53,k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
      | r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'),'#skF_3',D_53,D_53),D_53) ) ),
    inference(resolution,[status(thm)],[c_182,c_36])).

tff(c_213,plain,(
    ! [D_53] :
      ( r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'),'#skF_3',D_53,D_53),'#skF_4')
      | k4_subset_1(k1_zfmisc_1('#skF_2'),D_53,D_53) = '#skF_3'
      | ~ m1_subset_1(D_53,k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
      | r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'),'#skF_3',D_53,D_53),D_53) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_192])).

tff(c_596,plain,
    ( k4_subset_1(k1_zfmisc_1('#skF_2'),'#skF_4','#skF_4') = '#skF_3'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
    | r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'),'#skF_3','#skF_4','#skF_4'),'#skF_4') ),
    inference(factorization,[status(thm),theory(equality)],[c_213])).

tff(c_599,plain,
    ( '#skF_3' = '#skF_4'
    | r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'),'#skF_3','#skF_4','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_525,c_596])).

tff(c_600,plain,(
    r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'),'#skF_3','#skF_4','#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_599])).

tff(c_22,plain,(
    ! [D_20] :
      ( r2_hidden(D_20,'#skF_3')
      | ~ r2_hidden(D_20,'#skF_4')
      | ~ m1_subset_1(D_20,k1_zfmisc_1('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_37,plain,(
    ! [B_24,C_25,D_26] :
      ( r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'),B_24,C_25,D_26),'#skF_3')
      | ~ r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'),B_24,C_25,D_26),'#skF_4')
      | k4_subset_1(k1_zfmisc_1('#skF_2'),C_25,D_26) = B_24
      | ~ m1_subset_1(D_26,k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
      | ~ m1_subset_1(B_24,k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_27,c_22])).

tff(c_642,plain,
    ( ~ r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'),'#skF_3','#skF_4','#skF_4'),'#skF_3')
    | k4_subset_1(k1_zfmisc_1('#skF_2'),'#skF_4','#skF_4') = '#skF_3'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_600,c_4])).

tff(c_647,plain,
    ( ~ r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'),'#skF_3','#skF_4','#skF_4'),'#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_525,c_642])).

tff(c_648,plain,(
    ~ r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'),'#skF_3','#skF_4','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_647])).

tff(c_662,plain,
    ( ~ r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'),'#skF_3','#skF_4','#skF_4'),'#skF_4')
    | k4_subset_1(k1_zfmisc_1('#skF_2'),'#skF_4','#skF_4') = '#skF_3'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_37,c_648])).

tff(c_673,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_525,c_600,c_662])).

tff(c_675,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_673])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:23:44 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.67/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.37  
% 2.67/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.37  %$ r2_hidden > m1_subset_1 > k4_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.67/1.37  
% 2.67/1.37  %Foreground sorts:
% 2.67/1.37  
% 2.67/1.37  
% 2.67/1.37  %Background operators:
% 2.67/1.37  
% 2.67/1.37  
% 2.67/1.37  %Foreground operators:
% 2.67/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.67/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.67/1.37  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.67/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.67/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.67/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.67/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.67/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.67/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.67/1.37  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.67/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.67/1.37  
% 2.67/1.38  tff(f_59, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, B) <=> r2_hidden(D, C)))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_setfam_1)).
% 2.67/1.38  tff(f_44, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => ((![E]: (m1_subset_1(E, A) => (r2_hidden(E, B) <=> (r2_hidden(E, C) | r2_hidden(E, D))))) => (B = k4_subset_1(A, C, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_subset_1)).
% 2.67/1.38  tff(c_16, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.67/1.38  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.67/1.38  tff(c_18, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.67/1.38  tff(c_14, plain, (![A_1, B_2, C_10, D_14]: (r2_hidden('#skF_1'(A_1, B_2, C_10, D_14), B_2) | r2_hidden('#skF_1'(A_1, B_2, C_10, D_14), D_14) | r2_hidden('#skF_1'(A_1, B_2, C_10, D_14), C_10) | k4_subset_1(A_1, C_10, D_14)=B_2 | ~m1_subset_1(D_14, k1_zfmisc_1(A_1)) | ~m1_subset_1(C_10, k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.67/1.38  tff(c_110, plain, (![A_1, B_2, D_14]: (r2_hidden('#skF_1'(A_1, B_2, D_14, D_14), B_2) | k4_subset_1(A_1, D_14, D_14)=B_2 | ~m1_subset_1(D_14, k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)) | r2_hidden('#skF_1'(A_1, B_2, D_14, D_14), D_14))), inference(factorization, [status(thm), theory('equality')], [c_14])).
% 2.67/1.38  tff(c_180, plain, (![A_1, B_2]: (k4_subset_1(A_1, B_2, B_2)=B_2 | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)) | r2_hidden('#skF_1'(A_1, B_2, B_2, B_2), B_2))), inference(factorization, [status(thm), theory('equality')], [c_110])).
% 2.67/1.38  tff(c_219, plain, (![A_54, B_55]: (k4_subset_1(A_54, B_55, B_55)=B_55 | ~m1_subset_1(B_55, k1_zfmisc_1(A_54)) | r2_hidden('#skF_1'(A_54, B_55, B_55, B_55), B_55))), inference(factorization, [status(thm), theory('equality')], [c_110])).
% 2.67/1.38  tff(c_4, plain, (![A_1, B_2, C_10, D_14]: (~r2_hidden('#skF_1'(A_1, B_2, C_10, D_14), D_14) | ~r2_hidden('#skF_1'(A_1, B_2, C_10, D_14), B_2) | k4_subset_1(A_1, C_10, D_14)=B_2 | ~m1_subset_1(D_14, k1_zfmisc_1(A_1)) | ~m1_subset_1(C_10, k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.67/1.38  tff(c_490, plain, (![A_67, B_68]: (~r2_hidden('#skF_1'(A_67, B_68, B_68, B_68), B_68) | k4_subset_1(A_67, B_68, B_68)=B_68 | ~m1_subset_1(B_68, k1_zfmisc_1(A_67)))), inference(resolution, [status(thm)], [c_219, c_4])).
% 2.67/1.38  tff(c_516, plain, (![A_69, B_70]: (k4_subset_1(A_69, B_70, B_70)=B_70 | ~m1_subset_1(B_70, k1_zfmisc_1(A_69)))), inference(resolution, [status(thm)], [c_180, c_490])).
% 2.67/1.38  tff(c_525, plain, (k4_subset_1(k1_zfmisc_1('#skF_2'), '#skF_4', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_18, c_516])).
% 2.67/1.38  tff(c_182, plain, (![A_51, B_52, D_53]: (r2_hidden('#skF_1'(A_51, B_52, D_53, D_53), B_52) | k4_subset_1(A_51, D_53, D_53)=B_52 | ~m1_subset_1(D_53, k1_zfmisc_1(A_51)) | ~m1_subset_1(B_52, k1_zfmisc_1(A_51)) | r2_hidden('#skF_1'(A_51, B_52, D_53, D_53), D_53))), inference(factorization, [status(thm), theory('equality')], [c_14])).
% 2.67/1.38  tff(c_27, plain, (![A_23, B_24, C_25, D_26]: (m1_subset_1('#skF_1'(A_23, B_24, C_25, D_26), A_23) | k4_subset_1(A_23, C_25, D_26)=B_24 | ~m1_subset_1(D_26, k1_zfmisc_1(A_23)) | ~m1_subset_1(C_25, k1_zfmisc_1(A_23)) | ~m1_subset_1(B_24, k1_zfmisc_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.67/1.38  tff(c_24, plain, (![D_20]: (r2_hidden(D_20, '#skF_4') | ~r2_hidden(D_20, '#skF_3') | ~m1_subset_1(D_20, k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.67/1.38  tff(c_36, plain, (![B_24, C_25, D_26]: (r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'), B_24, C_25, D_26), '#skF_4') | ~r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'), B_24, C_25, D_26), '#skF_3') | k4_subset_1(k1_zfmisc_1('#skF_2'), C_25, D_26)=B_24 | ~m1_subset_1(D_26, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~m1_subset_1(C_25, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~m1_subset_1(B_24, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))))), inference(resolution, [status(thm)], [c_27, c_24])).
% 2.67/1.38  tff(c_192, plain, (![D_53]: (r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'), '#skF_3', D_53, D_53), '#skF_4') | k4_subset_1(k1_zfmisc_1('#skF_2'), D_53, D_53)='#skF_3' | ~m1_subset_1(D_53, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'), '#skF_3', D_53, D_53), D_53))), inference(resolution, [status(thm)], [c_182, c_36])).
% 2.67/1.38  tff(c_213, plain, (![D_53]: (r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'), '#skF_3', D_53, D_53), '#skF_4') | k4_subset_1(k1_zfmisc_1('#skF_2'), D_53, D_53)='#skF_3' | ~m1_subset_1(D_53, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'), '#skF_3', D_53, D_53), D_53))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_192])).
% 2.67/1.38  tff(c_596, plain, (k4_subset_1(k1_zfmisc_1('#skF_2'), '#skF_4', '#skF_4')='#skF_3' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'), '#skF_3', '#skF_4', '#skF_4'), '#skF_4')), inference(factorization, [status(thm), theory('equality')], [c_213])).
% 2.67/1.38  tff(c_599, plain, ('#skF_3'='#skF_4' | r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'), '#skF_3', '#skF_4', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_525, c_596])).
% 2.67/1.38  tff(c_600, plain, (r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'), '#skF_3', '#skF_4', '#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_16, c_599])).
% 2.67/1.38  tff(c_22, plain, (![D_20]: (r2_hidden(D_20, '#skF_3') | ~r2_hidden(D_20, '#skF_4') | ~m1_subset_1(D_20, k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.67/1.38  tff(c_37, plain, (![B_24, C_25, D_26]: (r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'), B_24, C_25, D_26), '#skF_3') | ~r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'), B_24, C_25, D_26), '#skF_4') | k4_subset_1(k1_zfmisc_1('#skF_2'), C_25, D_26)=B_24 | ~m1_subset_1(D_26, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~m1_subset_1(C_25, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~m1_subset_1(B_24, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))))), inference(resolution, [status(thm)], [c_27, c_22])).
% 2.67/1.38  tff(c_642, plain, (~r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'), '#skF_3', '#skF_4', '#skF_4'), '#skF_3') | k4_subset_1(k1_zfmisc_1('#skF_2'), '#skF_4', '#skF_4')='#skF_3' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_600, c_4])).
% 2.67/1.38  tff(c_647, plain, (~r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'), '#skF_3', '#skF_4', '#skF_4'), '#skF_3') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_525, c_642])).
% 2.67/1.38  tff(c_648, plain, (~r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'), '#skF_3', '#skF_4', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_16, c_647])).
% 2.67/1.38  tff(c_662, plain, (~r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'), '#skF_3', '#skF_4', '#skF_4'), '#skF_4') | k4_subset_1(k1_zfmisc_1('#skF_2'), '#skF_4', '#skF_4')='#skF_3' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_37, c_648])).
% 2.67/1.38  tff(c_673, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_525, c_600, c_662])).
% 2.67/1.38  tff(c_675, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_673])).
% 2.67/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.38  
% 2.67/1.38  Inference rules
% 2.67/1.38  ----------------------
% 2.67/1.38  #Ref     : 0
% 2.67/1.38  #Sup     : 80
% 2.67/1.38  #Fact    : 18
% 2.67/1.38  #Define  : 0
% 2.67/1.38  #Split   : 1
% 2.67/1.38  #Chain   : 0
% 2.67/1.38  #Close   : 0
% 2.67/1.38  
% 2.67/1.38  Ordering : KBO
% 2.67/1.38  
% 2.67/1.38  Simplification rules
% 2.67/1.38  ----------------------
% 2.67/1.38  #Subsume      : 24
% 2.67/1.38  #Demod        : 97
% 2.67/1.38  #Tautology    : 37
% 2.67/1.38  #SimpNegUnit  : 14
% 2.67/1.38  #BackRed      : 0
% 2.67/1.38  
% 2.67/1.38  #Partial instantiations: 0
% 2.67/1.38  #Strategies tried      : 1
% 2.67/1.38  
% 2.67/1.38  Timing (in seconds)
% 2.67/1.38  ----------------------
% 2.67/1.39  Preprocessing        : 0.28
% 2.67/1.39  Parsing              : 0.15
% 2.67/1.39  CNF conversion       : 0.02
% 2.67/1.39  Main loop            : 0.32
% 2.67/1.39  Inferencing          : 0.14
% 2.67/1.39  Reduction            : 0.08
% 2.67/1.39  Demodulation         : 0.06
% 2.67/1.39  BG Simplification    : 0.02
% 2.67/1.39  Subsumption          : 0.07
% 2.67/1.39  Abstraction          : 0.02
% 2.67/1.39  MUC search           : 0.00
% 2.67/1.39  Cooper               : 0.00
% 2.67/1.39  Total                : 0.63
% 2.67/1.39  Index Insertion      : 0.00
% 2.67/1.39  Index Deletion       : 0.00
% 2.67/1.39  Index Matching       : 0.00
% 2.67/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
