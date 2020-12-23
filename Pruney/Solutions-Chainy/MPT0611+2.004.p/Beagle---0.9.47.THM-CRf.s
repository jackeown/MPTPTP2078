%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:40 EST 2020

% Result     : Theorem 8.37s
% Output     : CNFRefutation 8.37s
% Verified   : 
% Statistics : Number of formulae       :   43 (  52 expanded)
%              Number of leaves         :   20 (  27 expanded)
%              Depth                    :   11
%              Number of atoms          :   70 ( 104 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_xboole_0(k2_relat_1(A),k2_relat_1(B))
             => r1_xboole_0(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t215_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( ( r1_xboole_0(A,B)
        | r1_xboole_0(C,D) )
     => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(c_22,plain,(
    ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_20,plain,(
    ! [A_17] :
      ( r1_tarski(A_17,k2_zfmisc_1(k1_relat_1(A_17),k2_relat_1(A_17)))
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_26,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_24,plain,(
    r1_xboole_0(k2_relat_1('#skF_3'),k2_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r2_hidden('#skF_2'(A_8,B_9),B_9)
      | r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_71,plain,(
    ! [C_35,B_36,A_37] :
      ( r2_hidden(C_35,B_36)
      | ~ r2_hidden(C_35,A_37)
      | ~ r1_tarski(A_37,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_78,plain,(
    ! [A_8,B_9,B_36] :
      ( r2_hidden('#skF_2'(A_8,B_9),B_36)
      | ~ r1_tarski(B_9,B_36)
      | r1_xboole_0(A_8,B_9) ) ),
    inference(resolution,[status(thm)],[c_12,c_71])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( r2_hidden('#skF_2'(A_8,B_9),A_8)
      | r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_79,plain,(
    ! [A_8,B_9,B_36] :
      ( r2_hidden('#skF_2'(A_8,B_9),B_36)
      | ~ r1_tarski(A_8,B_36)
      | r1_xboole_0(A_8,B_9) ) ),
    inference(resolution,[status(thm)],[c_14,c_71])).

tff(c_88,plain,(
    ! [C_42,D_43,A_44,B_45] :
      ( ~ r1_xboole_0(C_42,D_43)
      | r1_xboole_0(k2_zfmisc_1(A_44,C_42),k2_zfmisc_1(B_45,D_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_10,plain,(
    ! [A_8,B_9,C_12] :
      ( ~ r1_xboole_0(A_8,B_9)
      | ~ r2_hidden(C_12,B_9)
      | ~ r2_hidden(C_12,A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_265,plain,(
    ! [C_81,C_78,D_77,B_79,A_80] :
      ( ~ r2_hidden(C_81,k2_zfmisc_1(B_79,D_77))
      | ~ r2_hidden(C_81,k2_zfmisc_1(A_80,C_78))
      | ~ r1_xboole_0(C_78,D_77) ) ),
    inference(resolution,[status(thm)],[c_88,c_10])).

tff(c_2199,plain,(
    ! [D_392,B_393,A_390,A_391,B_395,C_394] :
      ( ~ r2_hidden('#skF_2'(A_391,B_393),k2_zfmisc_1(A_390,C_394))
      | ~ r1_xboole_0(C_394,D_392)
      | ~ r1_tarski(A_391,k2_zfmisc_1(B_395,D_392))
      | r1_xboole_0(A_391,B_393) ) ),
    inference(resolution,[status(thm)],[c_79,c_265])).

tff(c_7750,plain,(
    ! [C_919,A_917,A_915,B_918,B_914,D_916] :
      ( ~ r1_xboole_0(C_919,D_916)
      | ~ r1_tarski(A_915,k2_zfmisc_1(B_914,D_916))
      | ~ r1_tarski(B_918,k2_zfmisc_1(A_917,C_919))
      | r1_xboole_0(A_915,B_918) ) ),
    inference(resolution,[status(thm)],[c_78,c_2199])).

tff(c_8126,plain,(
    ! [A_938,B_939,B_940,A_941] :
      ( ~ r1_tarski(A_938,k2_zfmisc_1(B_939,k2_relat_1('#skF_4')))
      | ~ r1_tarski(B_940,k2_zfmisc_1(A_941,k2_relat_1('#skF_3')))
      | r1_xboole_0(A_938,B_940) ) ),
    inference(resolution,[status(thm)],[c_24,c_7750])).

tff(c_8129,plain,(
    ! [B_940,A_941] :
      ( ~ r1_tarski(B_940,k2_zfmisc_1(A_941,k2_relat_1('#skF_3')))
      | r1_xboole_0('#skF_4',B_940)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_20,c_8126])).

tff(c_8137,plain,(
    ! [B_942,A_943] :
      ( ~ r1_tarski(B_942,k2_zfmisc_1(A_943,k2_relat_1('#skF_3')))
      | r1_xboole_0('#skF_4',B_942) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_8129])).

tff(c_8141,plain,
    ( r1_xboole_0('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_8137])).

tff(c_8148,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_8141])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( r1_xboole_0(B_7,A_6)
      | ~ r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_8172,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_8148,c_8])).

tff(c_8186,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_8172])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:59:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.37/3.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.37/3.27  
% 8.37/3.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.37/3.28  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 8.37/3.28  
% 8.37/3.28  %Foreground sorts:
% 8.37/3.28  
% 8.37/3.28  
% 8.37/3.28  %Background operators:
% 8.37/3.28  
% 8.37/3.28  
% 8.37/3.28  %Foreground operators:
% 8.37/3.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.37/3.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.37/3.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.37/3.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.37/3.28  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.37/3.28  tff('#skF_3', type, '#skF_3': $i).
% 8.37/3.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.37/3.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.37/3.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.37/3.28  tff('#skF_4', type, '#skF_4': $i).
% 8.37/3.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.37/3.28  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.37/3.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.37/3.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.37/3.28  
% 8.37/3.29  tff(f_74, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_xboole_0(k2_relat_1(A), k2_relat_1(B)) => r1_xboole_0(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t215_relat_1)).
% 8.37/3.29  tff(f_64, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 8.37/3.29  tff(f_54, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 8.37/3.29  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 8.37/3.29  tff(f_60, axiom, (![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 8.37/3.29  tff(f_36, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 8.37/3.29  tff(c_22, plain, (~r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.37/3.29  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.37/3.29  tff(c_20, plain, (![A_17]: (r1_tarski(A_17, k2_zfmisc_1(k1_relat_1(A_17), k2_relat_1(A_17))) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.37/3.29  tff(c_26, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.37/3.29  tff(c_24, plain, (r1_xboole_0(k2_relat_1('#skF_3'), k2_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.37/3.29  tff(c_12, plain, (![A_8, B_9]: (r2_hidden('#skF_2'(A_8, B_9), B_9) | r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.37/3.29  tff(c_71, plain, (![C_35, B_36, A_37]: (r2_hidden(C_35, B_36) | ~r2_hidden(C_35, A_37) | ~r1_tarski(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.37/3.29  tff(c_78, plain, (![A_8, B_9, B_36]: (r2_hidden('#skF_2'(A_8, B_9), B_36) | ~r1_tarski(B_9, B_36) | r1_xboole_0(A_8, B_9))), inference(resolution, [status(thm)], [c_12, c_71])).
% 8.37/3.29  tff(c_14, plain, (![A_8, B_9]: (r2_hidden('#skF_2'(A_8, B_9), A_8) | r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.37/3.29  tff(c_79, plain, (![A_8, B_9, B_36]: (r2_hidden('#skF_2'(A_8, B_9), B_36) | ~r1_tarski(A_8, B_36) | r1_xboole_0(A_8, B_9))), inference(resolution, [status(thm)], [c_14, c_71])).
% 8.37/3.29  tff(c_88, plain, (![C_42, D_43, A_44, B_45]: (~r1_xboole_0(C_42, D_43) | r1_xboole_0(k2_zfmisc_1(A_44, C_42), k2_zfmisc_1(B_45, D_43)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.37/3.29  tff(c_10, plain, (![A_8, B_9, C_12]: (~r1_xboole_0(A_8, B_9) | ~r2_hidden(C_12, B_9) | ~r2_hidden(C_12, A_8))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.37/3.29  tff(c_265, plain, (![C_81, C_78, D_77, B_79, A_80]: (~r2_hidden(C_81, k2_zfmisc_1(B_79, D_77)) | ~r2_hidden(C_81, k2_zfmisc_1(A_80, C_78)) | ~r1_xboole_0(C_78, D_77))), inference(resolution, [status(thm)], [c_88, c_10])).
% 8.37/3.29  tff(c_2199, plain, (![D_392, B_393, A_390, A_391, B_395, C_394]: (~r2_hidden('#skF_2'(A_391, B_393), k2_zfmisc_1(A_390, C_394)) | ~r1_xboole_0(C_394, D_392) | ~r1_tarski(A_391, k2_zfmisc_1(B_395, D_392)) | r1_xboole_0(A_391, B_393))), inference(resolution, [status(thm)], [c_79, c_265])).
% 8.37/3.29  tff(c_7750, plain, (![C_919, A_917, A_915, B_918, B_914, D_916]: (~r1_xboole_0(C_919, D_916) | ~r1_tarski(A_915, k2_zfmisc_1(B_914, D_916)) | ~r1_tarski(B_918, k2_zfmisc_1(A_917, C_919)) | r1_xboole_0(A_915, B_918))), inference(resolution, [status(thm)], [c_78, c_2199])).
% 8.37/3.29  tff(c_8126, plain, (![A_938, B_939, B_940, A_941]: (~r1_tarski(A_938, k2_zfmisc_1(B_939, k2_relat_1('#skF_4'))) | ~r1_tarski(B_940, k2_zfmisc_1(A_941, k2_relat_1('#skF_3'))) | r1_xboole_0(A_938, B_940))), inference(resolution, [status(thm)], [c_24, c_7750])).
% 8.37/3.29  tff(c_8129, plain, (![B_940, A_941]: (~r1_tarski(B_940, k2_zfmisc_1(A_941, k2_relat_1('#skF_3'))) | r1_xboole_0('#skF_4', B_940) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_20, c_8126])).
% 8.37/3.29  tff(c_8137, plain, (![B_942, A_943]: (~r1_tarski(B_942, k2_zfmisc_1(A_943, k2_relat_1('#skF_3'))) | r1_xboole_0('#skF_4', B_942))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_8129])).
% 8.37/3.29  tff(c_8141, plain, (r1_xboole_0('#skF_4', '#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_8137])).
% 8.37/3.29  tff(c_8148, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_8141])).
% 8.37/3.29  tff(c_8, plain, (![B_7, A_6]: (r1_xboole_0(B_7, A_6) | ~r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.37/3.29  tff(c_8172, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_8148, c_8])).
% 8.37/3.29  tff(c_8186, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_8172])).
% 8.37/3.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.37/3.29  
% 8.37/3.29  Inference rules
% 8.37/3.29  ----------------------
% 8.37/3.29  #Ref     : 0
% 8.37/3.29  #Sup     : 2071
% 8.37/3.29  #Fact    : 0
% 8.37/3.29  #Define  : 0
% 8.37/3.29  #Split   : 4
% 8.37/3.29  #Chain   : 0
% 8.37/3.29  #Close   : 0
% 8.37/3.29  
% 8.37/3.29  Ordering : KBO
% 8.37/3.29  
% 8.37/3.29  Simplification rules
% 8.37/3.29  ----------------------
% 8.37/3.29  #Subsume      : 920
% 8.37/3.29  #Demod        : 47
% 8.37/3.29  #Tautology    : 41
% 8.37/3.29  #SimpNegUnit  : 1
% 8.37/3.29  #BackRed      : 0
% 8.37/3.29  
% 8.37/3.29  #Partial instantiations: 0
% 8.37/3.29  #Strategies tried      : 1
% 8.37/3.29  
% 8.37/3.29  Timing (in seconds)
% 8.37/3.29  ----------------------
% 8.37/3.29  Preprocessing        : 0.27
% 8.37/3.29  Parsing              : 0.15
% 8.37/3.29  CNF conversion       : 0.02
% 8.37/3.29  Main loop            : 2.23
% 8.37/3.29  Inferencing          : 0.49
% 8.37/3.29  Reduction            : 0.48
% 8.37/3.29  Demodulation         : 0.32
% 8.37/3.29  BG Simplification    : 0.04
% 8.37/3.29  Subsumption          : 1.09
% 8.37/3.29  Abstraction          : 0.06
% 8.37/3.29  MUC search           : 0.00
% 8.37/3.29  Cooper               : 0.00
% 8.37/3.29  Total                : 2.53
% 8.37/3.29  Index Insertion      : 0.00
% 8.37/3.29  Index Deletion       : 0.00
% 8.37/3.29  Index Matching       : 0.00
% 8.37/3.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
