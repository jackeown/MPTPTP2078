%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:49 EST 2020

% Result     : Theorem 1.57s
% Output     : CNFRefutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :   48 (  97 expanded)
%              Number of leaves         :   22 (  47 expanded)
%              Depth                    :    8
%              Number of atoms          :   71 ( 330 expanded)
%              Number of equality atoms :   25 (  93 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_64,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_funct_2)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(D)
          & r2_hidden(C,A) )
       => ( B = k1_xboole_0
          | k1_funct_1(k2_funct_1(D),k1_funct_1(D,C)) = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_8,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_22,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_20,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_16,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_18,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_12,plain,(
    r2_hidden('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_37,plain,(
    ! [D_13,C_14,B_15,A_16] :
      ( k1_funct_1(k2_funct_1(D_13),k1_funct_1(D_13,C_14)) = C_14
      | k1_xboole_0 = B_15
      | ~ r2_hidden(C_14,A_16)
      | ~ v2_funct_1(D_13)
      | ~ m1_subset_1(D_13,k1_zfmisc_1(k2_zfmisc_1(A_16,B_15)))
      | ~ v1_funct_2(D_13,A_16,B_15)
      | ~ v1_funct_1(D_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_44,plain,(
    ! [D_17,B_18] :
      ( k1_funct_1(k2_funct_1(D_17),k1_funct_1(D_17,'#skF_4')) = '#skF_4'
      | k1_xboole_0 = B_18
      | ~ v2_funct_1(D_17)
      | ~ m1_subset_1(D_17,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_18)))
      | ~ v1_funct_2(D_17,'#skF_1',B_18)
      | ~ v1_funct_1(D_17) ) ),
    inference(resolution,[status(thm)],[c_12,c_37])).

tff(c_46,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_4'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_44])).

tff(c_49,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_4'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_16,c_46])).

tff(c_50,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_49])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_60,plain,(
    ! [A_1] : r1_tarski('#skF_1',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2])).

tff(c_14,plain,(
    r2_hidden('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_28,plain,(
    ! [B_11,A_12] :
      ( ~ r1_tarski(B_11,A_12)
      | ~ r2_hidden(A_12,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_36,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_28])).

tff(c_69,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_36])).

tff(c_70,plain,(
    k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_49])).

tff(c_71,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_49])).

tff(c_10,plain,(
    k1_funct_1('#skF_2','#skF_3') = k1_funct_1('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_72,plain,(
    ! [D_21,B_22] :
      ( k1_funct_1(k2_funct_1(D_21),k1_funct_1(D_21,'#skF_3')) = '#skF_3'
      | k1_xboole_0 = B_22
      | ~ v2_funct_1(D_21)
      | ~ m1_subset_1(D_21,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_22)))
      | ~ v1_funct_2(D_21,'#skF_1',B_22)
      | ~ v1_funct_1(D_21) ) ),
    inference(resolution,[status(thm)],[c_14,c_37])).

tff(c_74,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_3')) = '#skF_3'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_72])).

tff(c_77,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_16,c_10,c_74])).

tff(c_78,plain,(
    k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_77])).

tff(c_83,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_78])).

tff(c_84,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_83])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:54:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.57/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.57/1.15  
% 1.57/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.57/1.15  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.57/1.15  
% 1.57/1.15  %Foreground sorts:
% 1.57/1.15  
% 1.57/1.15  
% 1.57/1.15  %Background operators:
% 1.57/1.15  
% 1.57/1.15  
% 1.57/1.15  %Foreground operators:
% 1.57/1.15  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.57/1.15  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 1.57/1.15  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.57/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.57/1.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.57/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.57/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.57/1.15  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.57/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.57/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.57/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.57/1.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.57/1.15  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.57/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.57/1.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.57/1.15  tff('#skF_4', type, '#skF_4': $i).
% 1.57/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.57/1.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.57/1.15  
% 1.57/1.16  tff(f_64, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) => (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_funct_2)).
% 1.57/1.16  tff(f_46, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(D) & r2_hidden(C, A)) => ((B = k1_xboole_0) | (k1_funct_1(k2_funct_1(D), k1_funct_1(D, C)) = C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_funct_2)).
% 1.57/1.16  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.57/1.16  tff(f_32, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 1.57/1.16  tff(c_8, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.57/1.16  tff(c_22, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.57/1.16  tff(c_20, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.57/1.16  tff(c_16, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.57/1.16  tff(c_18, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.57/1.16  tff(c_12, plain, (r2_hidden('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.57/1.16  tff(c_37, plain, (![D_13, C_14, B_15, A_16]: (k1_funct_1(k2_funct_1(D_13), k1_funct_1(D_13, C_14))=C_14 | k1_xboole_0=B_15 | ~r2_hidden(C_14, A_16) | ~v2_funct_1(D_13) | ~m1_subset_1(D_13, k1_zfmisc_1(k2_zfmisc_1(A_16, B_15))) | ~v1_funct_2(D_13, A_16, B_15) | ~v1_funct_1(D_13))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.57/1.16  tff(c_44, plain, (![D_17, B_18]: (k1_funct_1(k2_funct_1(D_17), k1_funct_1(D_17, '#skF_4'))='#skF_4' | k1_xboole_0=B_18 | ~v2_funct_1(D_17) | ~m1_subset_1(D_17, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_18))) | ~v1_funct_2(D_17, '#skF_1', B_18) | ~v1_funct_1(D_17))), inference(resolution, [status(thm)], [c_12, c_37])).
% 1.57/1.16  tff(c_46, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_4' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_18, c_44])).
% 1.57/1.16  tff(c_49, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_4' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_16, c_46])).
% 1.57/1.16  tff(c_50, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_49])).
% 1.57/1.16  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.57/1.16  tff(c_60, plain, (![A_1]: (r1_tarski('#skF_1', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_2])).
% 1.57/1.16  tff(c_14, plain, (r2_hidden('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.57/1.16  tff(c_28, plain, (![B_11, A_12]: (~r1_tarski(B_11, A_12) | ~r2_hidden(A_12, B_11))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.57/1.16  tff(c_36, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_14, c_28])).
% 1.57/1.16  tff(c_69, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_36])).
% 1.57/1.16  tff(c_70, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_4'), inference(splitRight, [status(thm)], [c_49])).
% 1.57/1.16  tff(c_71, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_49])).
% 1.57/1.16  tff(c_10, plain, (k1_funct_1('#skF_2', '#skF_3')=k1_funct_1('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.57/1.16  tff(c_72, plain, (![D_21, B_22]: (k1_funct_1(k2_funct_1(D_21), k1_funct_1(D_21, '#skF_3'))='#skF_3' | k1_xboole_0=B_22 | ~v2_funct_1(D_21) | ~m1_subset_1(D_21, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_22))) | ~v1_funct_2(D_21, '#skF_1', B_22) | ~v1_funct_1(D_21))), inference(resolution, [status(thm)], [c_14, c_37])).
% 1.57/1.16  tff(c_74, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_3'))='#skF_3' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_18, c_72])).
% 1.57/1.16  tff(c_77, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_16, c_10, c_74])).
% 1.57/1.16  tff(c_78, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_71, c_77])).
% 1.57/1.16  tff(c_83, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_78])).
% 1.57/1.16  tff(c_84, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8, c_83])).
% 1.57/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.57/1.16  
% 1.57/1.16  Inference rules
% 1.57/1.16  ----------------------
% 1.57/1.16  #Ref     : 0
% 1.57/1.16  #Sup     : 13
% 1.57/1.16  #Fact    : 0
% 1.57/1.16  #Define  : 0
% 1.57/1.16  #Split   : 1
% 1.57/1.16  #Chain   : 0
% 1.57/1.16  #Close   : 0
% 1.57/1.16  
% 1.57/1.16  Ordering : KBO
% 1.57/1.16  
% 1.57/1.16  Simplification rules
% 1.57/1.16  ----------------------
% 1.57/1.16  #Subsume      : 0
% 1.57/1.16  #Demod        : 18
% 1.57/1.16  #Tautology    : 6
% 1.57/1.16  #SimpNegUnit  : 2
% 1.57/1.16  #BackRed      : 6
% 1.57/1.16  
% 1.57/1.16  #Partial instantiations: 0
% 1.57/1.16  #Strategies tried      : 1
% 1.57/1.16  
% 1.57/1.16  Timing (in seconds)
% 1.57/1.16  ----------------------
% 1.57/1.16  Preprocessing        : 0.27
% 1.57/1.16  Parsing              : 0.14
% 1.57/1.16  CNF conversion       : 0.02
% 1.57/1.16  Main loop            : 0.12
% 1.57/1.16  Inferencing          : 0.04
% 1.57/1.16  Reduction            : 0.04
% 1.57/1.16  Demodulation         : 0.03
% 1.57/1.16  BG Simplification    : 0.01
% 1.57/1.16  Subsumption          : 0.01
% 1.57/1.16  Abstraction          : 0.01
% 1.57/1.16  MUC search           : 0.00
% 1.57/1.16  Cooper               : 0.00
% 1.57/1.16  Total                : 0.41
% 1.57/1.16  Index Insertion      : 0.00
% 1.57/1.16  Index Deletion       : 0.00
% 1.57/1.16  Index Matching       : 0.00
% 1.57/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
