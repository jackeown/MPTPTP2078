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
% DateTime   : Thu Dec  3 10:15:48 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 102 expanded)
%              Number of leaves         :   23 (  50 expanded)
%              Depth                    :    8
%              Number of atoms          :   71 ( 348 expanded)
%              Number of equality atoms :   25 (  99 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

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

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_10,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_14,plain,(
    r2_hidden('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_25,plain,(
    ! [B_11,A_12] :
      ( ~ r2_hidden(B_11,A_12)
      | ~ v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_32,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_25])).

tff(c_24,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_22,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_18,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_12,plain,(
    k1_funct_1('#skF_3','#skF_5') = k1_funct_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_43,plain,(
    ! [D_14,C_15,B_16,A_17] :
      ( k1_funct_1(k2_funct_1(D_14),k1_funct_1(D_14,C_15)) = C_15
      | k1_xboole_0 = B_16
      | ~ r2_hidden(C_15,A_17)
      | ~ v2_funct_1(D_14)
      | ~ m1_subset_1(D_14,k1_zfmisc_1(k2_zfmisc_1(A_17,B_16)))
      | ~ v1_funct_2(D_14,A_17,B_16)
      | ~ v1_funct_1(D_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_53,plain,(
    ! [D_18,B_19] :
      ( k1_funct_1(k2_funct_1(D_18),k1_funct_1(D_18,'#skF_5')) = '#skF_5'
      | k1_xboole_0 = B_19
      | ~ v2_funct_1(D_18)
      | ~ m1_subset_1(D_18,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_19)))
      | ~ v1_funct_2(D_18,'#skF_2',B_19)
      | ~ v1_funct_1(D_18) ) ),
    inference(resolution,[status(thm)],[c_14,c_43])).

tff(c_55,plain,
    ( k1_funct_1(k2_funct_1('#skF_3'),k1_funct_1('#skF_3','#skF_5')) = '#skF_5'
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_53])).

tff(c_58,plain,
    ( k1_funct_1(k2_funct_1('#skF_3'),k1_funct_1('#skF_3','#skF_4')) = '#skF_5'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_18,c_12,c_55])).

tff(c_65,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_69,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_6])).

tff(c_71,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_69])).

tff(c_73,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_16,plain,(
    r2_hidden('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_59,plain,(
    ! [D_20,B_21] :
      ( k1_funct_1(k2_funct_1(D_20),k1_funct_1(D_20,'#skF_4')) = '#skF_4'
      | k1_xboole_0 = B_21
      | ~ v2_funct_1(D_20)
      | ~ m1_subset_1(D_20,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_21)))
      | ~ v1_funct_2(D_20,'#skF_2',B_21)
      | ~ v1_funct_1(D_20) ) ),
    inference(resolution,[status(thm)],[c_16,c_43])).

tff(c_61,plain,
    ( k1_funct_1(k2_funct_1('#skF_3'),k1_funct_1('#skF_3','#skF_4')) = '#skF_4'
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_59])).

tff(c_64,plain,
    ( k1_funct_1(k2_funct_1('#skF_3'),k1_funct_1('#skF_3','#skF_4')) = '#skF_4'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_18,c_61])).

tff(c_74,plain,(
    k1_funct_1(k2_funct_1('#skF_3'),k1_funct_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_64])).

tff(c_72,plain,(
    k1_funct_1(k2_funct_1('#skF_3'),k1_funct_1('#skF_3','#skF_4')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_79,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72])).

tff(c_80,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_79])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:15:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.14  
% 1.63/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.14  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 1.63/1.14  
% 1.63/1.14  %Foreground sorts:
% 1.63/1.14  
% 1.63/1.14  
% 1.63/1.14  %Background operators:
% 1.63/1.14  
% 1.63/1.14  
% 1.63/1.14  %Foreground operators:
% 1.63/1.14  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.63/1.14  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 1.63/1.14  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.63/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.63/1.14  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.63/1.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.63/1.14  tff('#skF_5', type, '#skF_5': $i).
% 1.63/1.14  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.63/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.63/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.63/1.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.63/1.14  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.63/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.14  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.63/1.14  tff('#skF_4', type, '#skF_4': $i).
% 1.63/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.14  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.63/1.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.63/1.14  
% 1.63/1.15  tff(f_64, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) => (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_funct_2)).
% 1.63/1.15  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.63/1.15  tff(f_46, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(D) & r2_hidden(C, A)) => ((B = k1_xboole_0) | (k1_funct_1(k2_funct_1(D), k1_funct_1(D, C)) = C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_funct_2)).
% 1.63/1.15  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.63/1.15  tff(c_10, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.63/1.15  tff(c_14, plain, (r2_hidden('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.63/1.15  tff(c_25, plain, (![B_11, A_12]: (~r2_hidden(B_11, A_12) | ~v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.63/1.15  tff(c_32, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_14, c_25])).
% 1.63/1.15  tff(c_24, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.63/1.15  tff(c_22, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.63/1.15  tff(c_18, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.63/1.15  tff(c_12, plain, (k1_funct_1('#skF_3', '#skF_5')=k1_funct_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.63/1.15  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.63/1.15  tff(c_43, plain, (![D_14, C_15, B_16, A_17]: (k1_funct_1(k2_funct_1(D_14), k1_funct_1(D_14, C_15))=C_15 | k1_xboole_0=B_16 | ~r2_hidden(C_15, A_17) | ~v2_funct_1(D_14) | ~m1_subset_1(D_14, k1_zfmisc_1(k2_zfmisc_1(A_17, B_16))) | ~v1_funct_2(D_14, A_17, B_16) | ~v1_funct_1(D_14))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.63/1.15  tff(c_53, plain, (![D_18, B_19]: (k1_funct_1(k2_funct_1(D_18), k1_funct_1(D_18, '#skF_5'))='#skF_5' | k1_xboole_0=B_19 | ~v2_funct_1(D_18) | ~m1_subset_1(D_18, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_19))) | ~v1_funct_2(D_18, '#skF_2', B_19) | ~v1_funct_1(D_18))), inference(resolution, [status(thm)], [c_14, c_43])).
% 1.63/1.15  tff(c_55, plain, (k1_funct_1(k2_funct_1('#skF_3'), k1_funct_1('#skF_3', '#skF_5'))='#skF_5' | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_53])).
% 1.63/1.15  tff(c_58, plain, (k1_funct_1(k2_funct_1('#skF_3'), k1_funct_1('#skF_3', '#skF_4'))='#skF_5' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_18, c_12, c_55])).
% 1.63/1.15  tff(c_65, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_58])).
% 1.63/1.15  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.63/1.15  tff(c_69, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_6])).
% 1.63/1.15  tff(c_71, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_69])).
% 1.63/1.15  tff(c_73, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_58])).
% 1.63/1.15  tff(c_16, plain, (r2_hidden('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.63/1.15  tff(c_59, plain, (![D_20, B_21]: (k1_funct_1(k2_funct_1(D_20), k1_funct_1(D_20, '#skF_4'))='#skF_4' | k1_xboole_0=B_21 | ~v2_funct_1(D_20) | ~m1_subset_1(D_20, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_21))) | ~v1_funct_2(D_20, '#skF_2', B_21) | ~v1_funct_1(D_20))), inference(resolution, [status(thm)], [c_16, c_43])).
% 1.63/1.15  tff(c_61, plain, (k1_funct_1(k2_funct_1('#skF_3'), k1_funct_1('#skF_3', '#skF_4'))='#skF_4' | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_59])).
% 1.63/1.15  tff(c_64, plain, (k1_funct_1(k2_funct_1('#skF_3'), k1_funct_1('#skF_3', '#skF_4'))='#skF_4' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_18, c_61])).
% 1.63/1.15  tff(c_74, plain, (k1_funct_1(k2_funct_1('#skF_3'), k1_funct_1('#skF_3', '#skF_4'))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_73, c_64])).
% 1.63/1.15  tff(c_72, plain, (k1_funct_1(k2_funct_1('#skF_3'), k1_funct_1('#skF_3', '#skF_4'))='#skF_5'), inference(splitRight, [status(thm)], [c_58])).
% 1.63/1.15  tff(c_79, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72])).
% 1.63/1.15  tff(c_80, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_79])).
% 1.63/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.15  
% 1.63/1.15  Inference rules
% 1.63/1.15  ----------------------
% 1.63/1.15  #Ref     : 0
% 1.63/1.15  #Sup     : 12
% 1.63/1.15  #Fact    : 0
% 1.63/1.15  #Define  : 0
% 1.63/1.15  #Split   : 1
% 1.63/1.15  #Chain   : 0
% 1.63/1.15  #Close   : 0
% 1.63/1.15  
% 1.63/1.15  Ordering : KBO
% 1.63/1.15  
% 1.63/1.15  Simplification rules
% 1.63/1.15  ----------------------
% 1.63/1.15  #Subsume      : 1
% 1.63/1.15  #Demod        : 12
% 1.63/1.15  #Tautology    : 5
% 1.63/1.15  #SimpNegUnit  : 3
% 1.63/1.15  #BackRed      : 4
% 1.63/1.15  
% 1.63/1.15  #Partial instantiations: 0
% 1.63/1.15  #Strategies tried      : 1
% 1.63/1.15  
% 1.63/1.15  Timing (in seconds)
% 1.63/1.15  ----------------------
% 1.63/1.15  Preprocessing        : 0.27
% 1.63/1.15  Parsing              : 0.14
% 1.63/1.15  CNF conversion       : 0.02
% 1.63/1.15  Main loop            : 0.12
% 1.63/1.15  Inferencing          : 0.05
% 1.63/1.15  Reduction            : 0.04
% 1.63/1.15  Demodulation         : 0.03
% 1.63/1.15  BG Simplification    : 0.01
% 1.63/1.15  Subsumption          : 0.02
% 1.63/1.15  Abstraction          : 0.01
% 1.63/1.15  MUC search           : 0.00
% 1.63/1.15  Cooper               : 0.00
% 1.63/1.15  Total                : 0.41
% 1.63/1.15  Index Insertion      : 0.00
% 1.63/1.15  Index Deletion       : 0.00
% 1.63/1.15  Index Matching       : 0.00
% 1.63/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
