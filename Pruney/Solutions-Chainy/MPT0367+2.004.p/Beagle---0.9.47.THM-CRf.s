%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:48 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :   46 (  81 expanded)
%              Number of leaves         :   16 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :   90 ( 216 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( ! [D] :
                  ( m1_subset_1(D,B)
                 => r2_hidden(D,C) )
             => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                 => r2_hidden(D,C) ) )
           => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

tff(c_18,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_22,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( m1_subset_1(B_4,A_3)
      | ~ v1_xboole_0(B_4)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_26,plain,(
    ! [D_19] :
      ( r2_hidden(D_19,'#skF_4')
      | ~ m1_subset_1(D_19,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_30,plain,(
    ! [D_19] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ m1_subset_1(D_19,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_2])).

tff(c_40,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_20,plain,(
    ! [D_16] :
      ( r2_hidden(D_16,'#skF_4')
      | ~ m1_subset_1(D_16,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_52,plain,(
    ! [B_26,A_27] :
      ( m1_subset_1(B_26,A_27)
      | ~ r2_hidden(B_26,A_27)
      | v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_58,plain,(
    ! [D_16] :
      ( m1_subset_1(D_16,'#skF_4')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(D_16,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_52])).

tff(c_63,plain,(
    ! [D_28] :
      ( m1_subset_1(D_28,'#skF_4')
      | ~ m1_subset_1(D_28,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_58])).

tff(c_68,plain,(
    ! [B_4] :
      ( m1_subset_1(B_4,'#skF_4')
      | ~ v1_xboole_0(B_4)
      | ~ v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_8,c_63])).

tff(c_69,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_81,plain,(
    ! [A_32,B_33,C_34] :
      ( r2_hidden('#skF_1'(A_32,B_33,C_34),B_33)
      | r1_tarski(B_33,C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(A_32))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( m1_subset_1(B_4,A_3)
      | ~ r2_hidden(B_4,A_3)
      | v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_215,plain,(
    ! [A_55,B_56,C_57] :
      ( m1_subset_1('#skF_1'(A_55,B_56,C_57),B_56)
      | v1_xboole_0(B_56)
      | r1_tarski(B_56,C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(A_55))
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_55)) ) ),
    inference(resolution,[status(thm)],[c_81,c_4])).

tff(c_70,plain,(
    ! [A_29,B_30,C_31] :
      ( ~ r2_hidden('#skF_1'(A_29,B_30,C_31),C_31)
      | r1_tarski(B_30,C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(A_29))
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_80,plain,(
    ! [B_30,A_29] :
      ( r1_tarski(B_30,'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_29))
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_29))
      | ~ m1_subset_1('#skF_1'(A_29,B_30,'#skF_4'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_70])).

tff(c_222,plain,(
    ! [A_55] :
      ( v1_xboole_0('#skF_3')
      | r1_tarski('#skF_3','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_55))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_55)) ) ),
    inference(resolution,[status(thm)],[c_215,c_80])).

tff(c_266,plain,(
    ! [A_58] :
      ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_58))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_58)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_69,c_18,c_222])).

tff(c_272,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_266])).

tff(c_277,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_272])).

tff(c_279,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_306,plain,(
    ! [A_66,B_67,C_68] :
      ( r2_hidden('#skF_1'(A_66,B_67,C_68),B_67)
      | r1_tarski(B_67,C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(A_66))
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_335,plain,(
    ! [B_71,C_72,A_73] :
      ( ~ v1_xboole_0(B_71)
      | r1_tarski(B_71,C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(A_73))
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_73)) ) ),
    inference(resolution,[status(thm)],[c_306,c_2])).

tff(c_352,plain,(
    ! [B_75] :
      ( ~ v1_xboole_0(B_75)
      | r1_tarski(B_75,'#skF_4')
      | ~ m1_subset_1(B_75,k1_zfmisc_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_22,c_335])).

tff(c_366,plain,
    ( ~ v1_xboole_0('#skF_3')
    | r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_352])).

tff(c_373,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_366])).

tff(c_375,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_373])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n004.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 15:45:53 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.29  
% 2.13/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.29  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.13/1.29  
% 2.13/1.29  %Foreground sorts:
% 2.13/1.29  
% 2.13/1.29  
% 2.13/1.29  %Background operators:
% 2.13/1.29  
% 2.13/1.29  
% 2.13/1.29  %Foreground operators:
% 2.13/1.29  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.13/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.13/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.13/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.13/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.13/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.13/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.13/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.13/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.13/1.29  
% 2.44/1.31  tff(f_70, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, B) => r2_hidden(D, C))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_subset_1)).
% 2.44/1.31  tff(f_43, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.44/1.31  tff(f_30, axiom, (![A, B]: ~(r2_hidden(A, B) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_boole)).
% 2.44/1.31  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_subset_1)).
% 2.44/1.31  tff(c_18, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.44/1.31  tff(c_22, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.44/1.31  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.44/1.31  tff(c_8, plain, (![B_4, A_3]: (m1_subset_1(B_4, A_3) | ~v1_xboole_0(B_4) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.44/1.31  tff(c_26, plain, (![D_19]: (r2_hidden(D_19, '#skF_4') | ~m1_subset_1(D_19, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.44/1.31  tff(c_2, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.44/1.31  tff(c_30, plain, (![D_19]: (~v1_xboole_0('#skF_4') | ~m1_subset_1(D_19, '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_2])).
% 2.44/1.31  tff(c_40, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_30])).
% 2.44/1.31  tff(c_20, plain, (![D_16]: (r2_hidden(D_16, '#skF_4') | ~m1_subset_1(D_16, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.44/1.31  tff(c_52, plain, (![B_26, A_27]: (m1_subset_1(B_26, A_27) | ~r2_hidden(B_26, A_27) | v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.44/1.31  tff(c_58, plain, (![D_16]: (m1_subset_1(D_16, '#skF_4') | v1_xboole_0('#skF_4') | ~m1_subset_1(D_16, '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_52])).
% 2.44/1.31  tff(c_63, plain, (![D_28]: (m1_subset_1(D_28, '#skF_4') | ~m1_subset_1(D_28, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_40, c_58])).
% 2.44/1.31  tff(c_68, plain, (![B_4]: (m1_subset_1(B_4, '#skF_4') | ~v1_xboole_0(B_4) | ~v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_8, c_63])).
% 2.44/1.31  tff(c_69, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_68])).
% 2.44/1.31  tff(c_81, plain, (![A_32, B_33, C_34]: (r2_hidden('#skF_1'(A_32, B_33, C_34), B_33) | r1_tarski(B_33, C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(A_32)) | ~m1_subset_1(B_33, k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.44/1.31  tff(c_4, plain, (![B_4, A_3]: (m1_subset_1(B_4, A_3) | ~r2_hidden(B_4, A_3) | v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.44/1.31  tff(c_215, plain, (![A_55, B_56, C_57]: (m1_subset_1('#skF_1'(A_55, B_56, C_57), B_56) | v1_xboole_0(B_56) | r1_tarski(B_56, C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(A_55)) | ~m1_subset_1(B_56, k1_zfmisc_1(A_55)))), inference(resolution, [status(thm)], [c_81, c_4])).
% 2.44/1.31  tff(c_70, plain, (![A_29, B_30, C_31]: (~r2_hidden('#skF_1'(A_29, B_30, C_31), C_31) | r1_tarski(B_30, C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(A_29)) | ~m1_subset_1(B_30, k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.44/1.31  tff(c_80, plain, (![B_30, A_29]: (r1_tarski(B_30, '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_29)) | ~m1_subset_1(B_30, k1_zfmisc_1(A_29)) | ~m1_subset_1('#skF_1'(A_29, B_30, '#skF_4'), '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_70])).
% 2.44/1.31  tff(c_222, plain, (![A_55]: (v1_xboole_0('#skF_3') | r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_55)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_55)))), inference(resolution, [status(thm)], [c_215, c_80])).
% 2.44/1.31  tff(c_266, plain, (![A_58]: (~m1_subset_1('#skF_4', k1_zfmisc_1(A_58)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_58)))), inference(negUnitSimplification, [status(thm)], [c_18, c_69, c_18, c_222])).
% 2.44/1.31  tff(c_272, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_266])).
% 2.44/1.31  tff(c_277, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_272])).
% 2.44/1.31  tff(c_279, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_68])).
% 2.44/1.31  tff(c_306, plain, (![A_66, B_67, C_68]: (r2_hidden('#skF_1'(A_66, B_67, C_68), B_67) | r1_tarski(B_67, C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(A_66)) | ~m1_subset_1(B_67, k1_zfmisc_1(A_66)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.44/1.31  tff(c_335, plain, (![B_71, C_72, A_73]: (~v1_xboole_0(B_71) | r1_tarski(B_71, C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(A_73)) | ~m1_subset_1(B_71, k1_zfmisc_1(A_73)))), inference(resolution, [status(thm)], [c_306, c_2])).
% 2.44/1.31  tff(c_352, plain, (![B_75]: (~v1_xboole_0(B_75) | r1_tarski(B_75, '#skF_4') | ~m1_subset_1(B_75, k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_22, c_335])).
% 2.44/1.31  tff(c_366, plain, (~v1_xboole_0('#skF_3') | r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_24, c_352])).
% 2.44/1.31  tff(c_373, plain, (r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_279, c_366])).
% 2.44/1.31  tff(c_375, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_373])).
% 2.44/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/1.31  
% 2.44/1.31  Inference rules
% 2.44/1.31  ----------------------
% 2.44/1.31  #Ref     : 0
% 2.44/1.31  #Sup     : 69
% 2.44/1.31  #Fact    : 0
% 2.44/1.31  #Define  : 0
% 2.44/1.31  #Split   : 6
% 2.44/1.31  #Chain   : 0
% 2.44/1.31  #Close   : 0
% 2.44/1.31  
% 2.44/1.31  Ordering : KBO
% 2.44/1.31  
% 2.44/1.31  Simplification rules
% 2.44/1.31  ----------------------
% 2.44/1.31  #Subsume      : 19
% 2.44/1.31  #Demod        : 5
% 2.44/1.31  #Tautology    : 3
% 2.44/1.31  #SimpNegUnit  : 11
% 2.44/1.31  #BackRed      : 0
% 2.44/1.31  
% 2.44/1.31  #Partial instantiations: 0
% 2.44/1.31  #Strategies tried      : 1
% 2.44/1.31  
% 2.44/1.31  Timing (in seconds)
% 2.44/1.31  ----------------------
% 2.44/1.31  Preprocessing        : 0.28
% 2.44/1.31  Parsing              : 0.15
% 2.44/1.31  CNF conversion       : 0.02
% 2.44/1.31  Main loop            : 0.28
% 2.44/1.31  Inferencing          : 0.11
% 2.44/1.31  Reduction            : 0.07
% 2.44/1.31  Demodulation         : 0.04
% 2.44/1.31  BG Simplification    : 0.02
% 2.44/1.31  Subsumption          : 0.06
% 2.44/1.31  Abstraction          : 0.01
% 2.44/1.31  MUC search           : 0.00
% 2.44/1.31  Cooper               : 0.00
% 2.44/1.31  Total                : 0.59
% 2.44/1.31  Index Insertion      : 0.00
% 2.44/1.31  Index Deletion       : 0.00
% 2.44/1.31  Index Matching       : 0.00
% 2.44/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
