%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:37 EST 2020

% Result     : Theorem 8.44s
% Output     : CNFRefutation 8.44s
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
           => ( r1_xboole_0(k1_relat_1(A),k1_relat_1(B))
             => r1_xboole_0(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t214_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( ( r1_xboole_0(A,B)
        | r1_xboole_0(C,D) )
     => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

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
    r1_xboole_0(k1_relat_1('#skF_3'),k1_relat_1('#skF_4')) ),
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

tff(c_81,plain,(
    ! [A_38,B_39,C_40,D_41] :
      ( ~ r1_xboole_0(A_38,B_39)
      | r1_xboole_0(k2_zfmisc_1(A_38,C_40),k2_zfmisc_1(B_39,D_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_10,plain,(
    ! [A_8,B_9,C_12] :
      ( ~ r1_xboole_0(A_8,B_9)
      | ~ r2_hidden(C_12,B_9)
      | ~ r2_hidden(C_12,A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_240,plain,(
    ! [B_73,C_74,A_72,C_76,D_75] :
      ( ~ r2_hidden(C_76,k2_zfmisc_1(B_73,D_75))
      | ~ r2_hidden(C_76,k2_zfmisc_1(A_72,C_74))
      | ~ r1_xboole_0(A_72,B_73) ) ),
    inference(resolution,[status(thm)],[c_81,c_10])).

tff(c_1807,plain,(
    ! [C_323,A_321,A_322,B_320,D_325,B_324] :
      ( ~ r2_hidden('#skF_2'(A_322,B_324),k2_zfmisc_1(A_321,C_323))
      | ~ r1_xboole_0(A_321,B_320)
      | ~ r1_tarski(A_322,k2_zfmisc_1(B_320,D_325))
      | r1_xboole_0(A_322,B_324) ) ),
    inference(resolution,[status(thm)],[c_79,c_240])).

tff(c_7561,plain,(
    ! [C_938,A_940,A_943,D_939,B_941,B_942] :
      ( ~ r1_xboole_0(A_943,B_942)
      | ~ r1_tarski(A_940,k2_zfmisc_1(B_942,D_939))
      | ~ r1_tarski(B_941,k2_zfmisc_1(A_943,C_938))
      | r1_xboole_0(A_940,B_941) ) ),
    inference(resolution,[status(thm)],[c_78,c_1807])).

tff(c_7761,plain,(
    ! [A_950,D_951,B_952,C_953] :
      ( ~ r1_tarski(A_950,k2_zfmisc_1(k1_relat_1('#skF_4'),D_951))
      | ~ r1_tarski(B_952,k2_zfmisc_1(k1_relat_1('#skF_3'),C_953))
      | r1_xboole_0(A_950,B_952) ) ),
    inference(resolution,[status(thm)],[c_24,c_7561])).

tff(c_7764,plain,(
    ! [B_952,C_953] :
      ( ~ r1_tarski(B_952,k2_zfmisc_1(k1_relat_1('#skF_3'),C_953))
      | r1_xboole_0('#skF_4',B_952)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_20,c_7761])).

tff(c_7772,plain,(
    ! [B_954,C_955] :
      ( ~ r1_tarski(B_954,k2_zfmisc_1(k1_relat_1('#skF_3'),C_955))
      | r1_xboole_0('#skF_4',B_954) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_7764])).

tff(c_7776,plain,
    ( r1_xboole_0('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_7772])).

tff(c_7783,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_7776])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( r1_xboole_0(B_7,A_6)
      | ~ r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_7807,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_7783,c_8])).

tff(c_7821,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_7807])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:50:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.44/3.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.44/3.15  
% 8.44/3.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.44/3.16  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 8.44/3.16  
% 8.44/3.16  %Foreground sorts:
% 8.44/3.16  
% 8.44/3.16  
% 8.44/3.16  %Background operators:
% 8.44/3.16  
% 8.44/3.16  
% 8.44/3.16  %Foreground operators:
% 8.44/3.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.44/3.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.44/3.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.44/3.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.44/3.16  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.44/3.16  tff('#skF_3', type, '#skF_3': $i).
% 8.44/3.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.44/3.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.44/3.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.44/3.16  tff('#skF_4', type, '#skF_4': $i).
% 8.44/3.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.44/3.16  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.44/3.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.44/3.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.44/3.16  
% 8.44/3.17  tff(f_74, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_xboole_0(k1_relat_1(A), k1_relat_1(B)) => r1_xboole_0(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t214_relat_1)).
% 8.44/3.17  tff(f_64, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 8.44/3.17  tff(f_54, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 8.44/3.17  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 8.44/3.17  tff(f_60, axiom, (![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 8.44/3.17  tff(f_36, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 8.44/3.17  tff(c_22, plain, (~r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.44/3.17  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.44/3.17  tff(c_20, plain, (![A_17]: (r1_tarski(A_17, k2_zfmisc_1(k1_relat_1(A_17), k2_relat_1(A_17))) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.44/3.17  tff(c_26, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.44/3.17  tff(c_24, plain, (r1_xboole_0(k1_relat_1('#skF_3'), k1_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.44/3.17  tff(c_12, plain, (![A_8, B_9]: (r2_hidden('#skF_2'(A_8, B_9), B_9) | r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.44/3.17  tff(c_71, plain, (![C_35, B_36, A_37]: (r2_hidden(C_35, B_36) | ~r2_hidden(C_35, A_37) | ~r1_tarski(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.44/3.17  tff(c_78, plain, (![A_8, B_9, B_36]: (r2_hidden('#skF_2'(A_8, B_9), B_36) | ~r1_tarski(B_9, B_36) | r1_xboole_0(A_8, B_9))), inference(resolution, [status(thm)], [c_12, c_71])).
% 8.44/3.17  tff(c_14, plain, (![A_8, B_9]: (r2_hidden('#skF_2'(A_8, B_9), A_8) | r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.44/3.17  tff(c_79, plain, (![A_8, B_9, B_36]: (r2_hidden('#skF_2'(A_8, B_9), B_36) | ~r1_tarski(A_8, B_36) | r1_xboole_0(A_8, B_9))), inference(resolution, [status(thm)], [c_14, c_71])).
% 8.44/3.17  tff(c_81, plain, (![A_38, B_39, C_40, D_41]: (~r1_xboole_0(A_38, B_39) | r1_xboole_0(k2_zfmisc_1(A_38, C_40), k2_zfmisc_1(B_39, D_41)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.44/3.17  tff(c_10, plain, (![A_8, B_9, C_12]: (~r1_xboole_0(A_8, B_9) | ~r2_hidden(C_12, B_9) | ~r2_hidden(C_12, A_8))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.44/3.17  tff(c_240, plain, (![B_73, C_74, A_72, C_76, D_75]: (~r2_hidden(C_76, k2_zfmisc_1(B_73, D_75)) | ~r2_hidden(C_76, k2_zfmisc_1(A_72, C_74)) | ~r1_xboole_0(A_72, B_73))), inference(resolution, [status(thm)], [c_81, c_10])).
% 8.44/3.17  tff(c_1807, plain, (![C_323, A_321, A_322, B_320, D_325, B_324]: (~r2_hidden('#skF_2'(A_322, B_324), k2_zfmisc_1(A_321, C_323)) | ~r1_xboole_0(A_321, B_320) | ~r1_tarski(A_322, k2_zfmisc_1(B_320, D_325)) | r1_xboole_0(A_322, B_324))), inference(resolution, [status(thm)], [c_79, c_240])).
% 8.44/3.17  tff(c_7561, plain, (![C_938, A_940, A_943, D_939, B_941, B_942]: (~r1_xboole_0(A_943, B_942) | ~r1_tarski(A_940, k2_zfmisc_1(B_942, D_939)) | ~r1_tarski(B_941, k2_zfmisc_1(A_943, C_938)) | r1_xboole_0(A_940, B_941))), inference(resolution, [status(thm)], [c_78, c_1807])).
% 8.44/3.17  tff(c_7761, plain, (![A_950, D_951, B_952, C_953]: (~r1_tarski(A_950, k2_zfmisc_1(k1_relat_1('#skF_4'), D_951)) | ~r1_tarski(B_952, k2_zfmisc_1(k1_relat_1('#skF_3'), C_953)) | r1_xboole_0(A_950, B_952))), inference(resolution, [status(thm)], [c_24, c_7561])).
% 8.44/3.17  tff(c_7764, plain, (![B_952, C_953]: (~r1_tarski(B_952, k2_zfmisc_1(k1_relat_1('#skF_3'), C_953)) | r1_xboole_0('#skF_4', B_952) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_20, c_7761])).
% 8.44/3.17  tff(c_7772, plain, (![B_954, C_955]: (~r1_tarski(B_954, k2_zfmisc_1(k1_relat_1('#skF_3'), C_955)) | r1_xboole_0('#skF_4', B_954))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_7764])).
% 8.44/3.17  tff(c_7776, plain, (r1_xboole_0('#skF_4', '#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_7772])).
% 8.44/3.17  tff(c_7783, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_7776])).
% 8.44/3.17  tff(c_8, plain, (![B_7, A_6]: (r1_xboole_0(B_7, A_6) | ~r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.44/3.17  tff(c_7807, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_7783, c_8])).
% 8.44/3.17  tff(c_7821, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_7807])).
% 8.44/3.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.44/3.17  
% 8.44/3.17  Inference rules
% 8.44/3.17  ----------------------
% 8.44/3.17  #Ref     : 0
% 8.44/3.17  #Sup     : 1974
% 8.44/3.17  #Fact    : 0
% 8.44/3.17  #Define  : 0
% 8.44/3.17  #Split   : 4
% 8.44/3.17  #Chain   : 0
% 8.44/3.17  #Close   : 0
% 8.44/3.17  
% 8.44/3.17  Ordering : KBO
% 8.44/3.17  
% 8.44/3.17  Simplification rules
% 8.44/3.17  ----------------------
% 8.44/3.17  #Subsume      : 823
% 8.44/3.17  #Demod        : 47
% 8.44/3.17  #Tautology    : 41
% 8.44/3.17  #SimpNegUnit  : 1
% 8.44/3.17  #BackRed      : 0
% 8.44/3.17  
% 8.44/3.17  #Partial instantiations: 0
% 8.44/3.17  #Strategies tried      : 1
% 8.44/3.17  
% 8.44/3.17  Timing (in seconds)
% 8.44/3.17  ----------------------
% 8.44/3.17  Preprocessing        : 0.28
% 8.44/3.17  Parsing              : 0.16
% 8.44/3.17  CNF conversion       : 0.02
% 8.44/3.17  Main loop            : 2.13
% 8.44/3.17  Inferencing          : 0.48
% 8.44/3.17  Reduction            : 0.45
% 8.44/3.17  Demodulation         : 0.30
% 8.44/3.17  BG Simplification    : 0.05
% 8.44/3.17  Subsumption          : 1.03
% 8.44/3.17  Abstraction          : 0.06
% 8.44/3.17  MUC search           : 0.00
% 8.44/3.17  Cooper               : 0.00
% 8.44/3.18  Total                : 2.44
% 8.44/3.18  Index Insertion      : 0.00
% 8.44/3.18  Index Deletion       : 0.00
% 8.44/3.18  Index Matching       : 0.00
% 8.44/3.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
