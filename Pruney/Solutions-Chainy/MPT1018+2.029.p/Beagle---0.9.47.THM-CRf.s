%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:49 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 214 expanded)
%              Number of leaves         :   24 (  89 expanded)
%              Depth                    :   11
%              Number of atoms          :   99 ( 776 expanded)
%              Number of equality atoms :   29 ( 210 expanded)
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

tff(f_73,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_funct_2)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(D)
          & r2_hidden(C,A) )
       => ( B = k1_xboole_0
          | k1_funct_1(k2_funct_1(D),k1_funct_1(D,C)) = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).

tff(f_31,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_29,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_14,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_28,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_26,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_22,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_18,plain,(
    r2_hidden('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_66,plain,(
    ! [D_24,C_25,B_26,A_27] :
      ( k1_funct_1(k2_funct_1(D_24),k1_funct_1(D_24,C_25)) = C_25
      | k1_xboole_0 = B_26
      | ~ r2_hidden(C_25,A_27)
      | ~ v2_funct_1(D_24)
      | ~ m1_subset_1(D_24,k1_zfmisc_1(k2_zfmisc_1(A_27,B_26)))
      | ~ v1_funct_2(D_24,A_27,B_26)
      | ~ v1_funct_1(D_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_84,plain,(
    ! [D_36,B_37] :
      ( k1_funct_1(k2_funct_1(D_36),k1_funct_1(D_36,'#skF_4')) = '#skF_4'
      | k1_xboole_0 = B_37
      | ~ v2_funct_1(D_36)
      | ~ m1_subset_1(D_36,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_37)))
      | ~ v1_funct_2(D_36,'#skF_1',B_37)
      | ~ v1_funct_1(D_36) ) ),
    inference(resolution,[status(thm)],[c_18,c_66])).

tff(c_89,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_4'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_84])).

tff(c_96,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_4'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_22,c_89])).

tff(c_98,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_36,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(A_18,B_19)
      | ~ m1_subset_1(A_18,k1_zfmisc_1(B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_48,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(resolution,[status(thm)],[c_4,c_36])).

tff(c_102,plain,(
    ! [A_2] : r1_tarski('#skF_1',A_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_48])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_56,plain,(
    ! [A_21,C_22,B_23] :
      ( m1_subset_1(A_21,C_22)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(C_22))
      | ~ r2_hidden(A_21,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_75,plain,(
    ! [A_31,B_32,A_33] :
      ( m1_subset_1(A_31,B_32)
      | ~ r2_hidden(A_31,A_33)
      | ~ r1_tarski(A_33,B_32) ) ),
    inference(resolution,[status(thm)],[c_8,c_56])).

tff(c_80,plain,(
    ! [B_32] :
      ( m1_subset_1('#skF_4',B_32)
      | ~ r1_tarski('#skF_1',B_32) ) ),
    inference(resolution,[status(thm)],[c_18,c_75])).

tff(c_140,plain,(
    ! [B_42] : m1_subset_1('#skF_4',B_42) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_80])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_153,plain,(
    ! [B_4] : r1_tarski('#skF_4',B_4) ),
    inference(resolution,[status(thm)],[c_140,c_6])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_171,plain,(
    ! [A_46] :
      ( A_46 = '#skF_1'
      | ~ r1_tarski(A_46,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_98,c_2])).

tff(c_184,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_153,c_171])).

tff(c_20,plain,(
    r2_hidden('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_81,plain,(
    ! [B_32] :
      ( m1_subset_1('#skF_3',B_32)
      | ~ r1_tarski('#skF_1',B_32) ) ),
    inference(resolution,[status(thm)],[c_20,c_75])).

tff(c_126,plain,(
    ! [B_41] : m1_subset_1('#skF_3',B_41) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_81])).

tff(c_139,plain,(
    ! [B_4] : r1_tarski('#skF_3',B_4) ),
    inference(resolution,[status(thm)],[c_126,c_6])).

tff(c_185,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_139,c_171])).

tff(c_208,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_185])).

tff(c_209,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_208])).

tff(c_211,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_210,plain,(
    k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_4')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_16,plain,(
    k1_funct_1('#skF_2','#skF_3') = k1_funct_1('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_216,plain,(
    ! [D_49,B_50] :
      ( k1_funct_1(k2_funct_1(D_49),k1_funct_1(D_49,'#skF_3')) = '#skF_3'
      | k1_xboole_0 = B_50
      | ~ v2_funct_1(D_49)
      | ~ m1_subset_1(D_49,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_50)))
      | ~ v1_funct_2(D_49,'#skF_1',B_50)
      | ~ v1_funct_1(D_49) ) ),
    inference(resolution,[status(thm)],[c_20,c_66])).

tff(c_221,plain,
    ( k1_funct_1(k2_funct_1('#skF_2'),k1_funct_1('#skF_2','#skF_3')) = '#skF_3'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_216])).

tff(c_228,plain,
    ( '#skF_3' = '#skF_4'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_22,c_210,c_16,c_221])).

tff(c_230,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_211,c_14,c_228])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:47:41 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.25/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.32  
% 2.25/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.32  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.25/1.32  
% 2.25/1.32  %Foreground sorts:
% 2.25/1.32  
% 2.25/1.32  
% 2.25/1.32  %Background operators:
% 2.25/1.32  
% 2.25/1.32  
% 2.25/1.32  %Foreground operators:
% 2.25/1.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.25/1.32  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.25/1.32  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.25/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.25/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.25/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.25/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.25/1.32  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.25/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.25/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.25/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.25/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.25/1.32  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.25/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.25/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.25/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.25/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.25/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.25/1.32  
% 2.25/1.33  tff(f_73, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) => (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_funct_2)).
% 2.25/1.33  tff(f_55, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(D) & r2_hidden(C, A)) => ((B = k1_xboole_0) | (k1_funct_1(k2_funct_1(D), k1_funct_1(D, C)) = C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_funct_2)).
% 2.25/1.33  tff(f_31, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.25/1.33  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.25/1.33  tff(f_41, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.25/1.33  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.25/1.33  tff(c_14, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.25/1.33  tff(c_28, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.25/1.33  tff(c_26, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.25/1.33  tff(c_22, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.25/1.33  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.25/1.33  tff(c_18, plain, (r2_hidden('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.25/1.33  tff(c_66, plain, (![D_24, C_25, B_26, A_27]: (k1_funct_1(k2_funct_1(D_24), k1_funct_1(D_24, C_25))=C_25 | k1_xboole_0=B_26 | ~r2_hidden(C_25, A_27) | ~v2_funct_1(D_24) | ~m1_subset_1(D_24, k1_zfmisc_1(k2_zfmisc_1(A_27, B_26))) | ~v1_funct_2(D_24, A_27, B_26) | ~v1_funct_1(D_24))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.25/1.33  tff(c_84, plain, (![D_36, B_37]: (k1_funct_1(k2_funct_1(D_36), k1_funct_1(D_36, '#skF_4'))='#skF_4' | k1_xboole_0=B_37 | ~v2_funct_1(D_36) | ~m1_subset_1(D_36, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_37))) | ~v1_funct_2(D_36, '#skF_1', B_37) | ~v1_funct_1(D_36))), inference(resolution, [status(thm)], [c_18, c_66])).
% 2.25/1.33  tff(c_89, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_4' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_24, c_84])).
% 2.25/1.33  tff(c_96, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_4' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_22, c_89])).
% 2.25/1.33  tff(c_98, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_96])).
% 2.25/1.33  tff(c_4, plain, (![A_2]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.25/1.33  tff(c_36, plain, (![A_18, B_19]: (r1_tarski(A_18, B_19) | ~m1_subset_1(A_18, k1_zfmisc_1(B_19)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.25/1.33  tff(c_48, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(resolution, [status(thm)], [c_4, c_36])).
% 2.25/1.33  tff(c_102, plain, (![A_2]: (r1_tarski('#skF_1', A_2))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_48])).
% 2.25/1.33  tff(c_8, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.25/1.33  tff(c_56, plain, (![A_21, C_22, B_23]: (m1_subset_1(A_21, C_22) | ~m1_subset_1(B_23, k1_zfmisc_1(C_22)) | ~r2_hidden(A_21, B_23))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.25/1.33  tff(c_75, plain, (![A_31, B_32, A_33]: (m1_subset_1(A_31, B_32) | ~r2_hidden(A_31, A_33) | ~r1_tarski(A_33, B_32))), inference(resolution, [status(thm)], [c_8, c_56])).
% 2.25/1.33  tff(c_80, plain, (![B_32]: (m1_subset_1('#skF_4', B_32) | ~r1_tarski('#skF_1', B_32))), inference(resolution, [status(thm)], [c_18, c_75])).
% 2.25/1.33  tff(c_140, plain, (![B_42]: (m1_subset_1('#skF_4', B_42))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_80])).
% 2.25/1.33  tff(c_6, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.25/1.33  tff(c_153, plain, (![B_4]: (r1_tarski('#skF_4', B_4))), inference(resolution, [status(thm)], [c_140, c_6])).
% 2.25/1.33  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.25/1.33  tff(c_171, plain, (![A_46]: (A_46='#skF_1' | ~r1_tarski(A_46, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_98, c_2])).
% 2.25/1.33  tff(c_184, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_153, c_171])).
% 2.25/1.33  tff(c_20, plain, (r2_hidden('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.25/1.33  tff(c_81, plain, (![B_32]: (m1_subset_1('#skF_3', B_32) | ~r1_tarski('#skF_1', B_32))), inference(resolution, [status(thm)], [c_20, c_75])).
% 2.25/1.33  tff(c_126, plain, (![B_41]: (m1_subset_1('#skF_3', B_41))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_81])).
% 2.25/1.33  tff(c_139, plain, (![B_4]: (r1_tarski('#skF_3', B_4))), inference(resolution, [status(thm)], [c_126, c_6])).
% 2.25/1.33  tff(c_185, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_139, c_171])).
% 2.25/1.33  tff(c_208, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_184, c_185])).
% 2.25/1.33  tff(c_209, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_208])).
% 2.25/1.33  tff(c_211, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_96])).
% 2.25/1.33  tff(c_210, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_4'))='#skF_4'), inference(splitRight, [status(thm)], [c_96])).
% 2.25/1.33  tff(c_16, plain, (k1_funct_1('#skF_2', '#skF_3')=k1_funct_1('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.25/1.33  tff(c_216, plain, (![D_49, B_50]: (k1_funct_1(k2_funct_1(D_49), k1_funct_1(D_49, '#skF_3'))='#skF_3' | k1_xboole_0=B_50 | ~v2_funct_1(D_49) | ~m1_subset_1(D_49, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_50))) | ~v1_funct_2(D_49, '#skF_1', B_50) | ~v1_funct_1(D_49))), inference(resolution, [status(thm)], [c_20, c_66])).
% 2.25/1.33  tff(c_221, plain, (k1_funct_1(k2_funct_1('#skF_2'), k1_funct_1('#skF_2', '#skF_3'))='#skF_3' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_24, c_216])).
% 2.25/1.33  tff(c_228, plain, ('#skF_3'='#skF_4' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_22, c_210, c_16, c_221])).
% 2.25/1.33  tff(c_230, plain, $false, inference(negUnitSimplification, [status(thm)], [c_211, c_14, c_228])).
% 2.25/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.33  
% 2.25/1.33  Inference rules
% 2.25/1.33  ----------------------
% 2.25/1.33  #Ref     : 0
% 2.25/1.33  #Sup     : 39
% 2.25/1.33  #Fact    : 0
% 2.25/1.33  #Define  : 0
% 2.25/1.33  #Split   : 2
% 2.25/1.33  #Chain   : 0
% 2.25/1.33  #Close   : 0
% 2.25/1.33  
% 2.25/1.33  Ordering : KBO
% 2.25/1.33  
% 2.25/1.33  Simplification rules
% 2.25/1.33  ----------------------
% 2.25/1.33  #Subsume      : 1
% 2.25/1.33  #Demod        : 52
% 2.25/1.33  #Tautology    : 15
% 2.25/1.33  #SimpNegUnit  : 2
% 2.25/1.33  #BackRed      : 20
% 2.25/1.33  
% 2.25/1.33  #Partial instantiations: 0
% 2.25/1.33  #Strategies tried      : 1
% 2.25/1.33  
% 2.25/1.33  Timing (in seconds)
% 2.25/1.33  ----------------------
% 2.25/1.34  Preprocessing        : 0.32
% 2.25/1.34  Parsing              : 0.17
% 2.25/1.34  CNF conversion       : 0.02
% 2.25/1.34  Main loop            : 0.21
% 2.25/1.34  Inferencing          : 0.07
% 2.25/1.34  Reduction            : 0.07
% 2.25/1.34  Demodulation         : 0.05
% 2.25/1.34  BG Simplification    : 0.01
% 2.25/1.34  Subsumption          : 0.03
% 2.25/1.34  Abstraction          : 0.01
% 2.25/1.34  MUC search           : 0.00
% 2.25/1.34  Cooper               : 0.00
% 2.25/1.34  Total                : 0.56
% 2.25/1.34  Index Insertion      : 0.00
% 2.25/1.34  Index Deletion       : 0.00
% 2.25/1.34  Index Matching       : 0.00
% 2.25/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
