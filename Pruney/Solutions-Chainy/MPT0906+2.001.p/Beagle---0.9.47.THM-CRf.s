%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:54 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 210 expanded)
%              Number of leaves         :   22 (  74 expanded)
%              Depth                    :    6
%              Number of atoms          :   99 ( 472 expanded)
%              Number of equality atoms :   53 ( 316 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_93,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) != k1_xboole_0
       => ! [C] :
            ( m1_subset_1(C,k2_zfmisc_1(A,B))
           => ( C != k1_mcart_1(C)
              & C != k2_mcart_1(C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_mcart_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ! [C] :
              ( m1_subset_1(C,k2_zfmisc_1(A,B))
             => ( C != k1_mcart_1(C)
                & C != k2_mcart_1(C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_mcart_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(c_24,plain,
    ( k2_mcart_1('#skF_3') = '#skF_3'
    | k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_43,plain,(
    k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_422,plain,(
    ! [C_48,A_49,B_50] :
      ( k1_mcart_1(C_48) != C_48
      | ~ m1_subset_1(C_48,k2_zfmisc_1(A_49,B_50))
      | k1_xboole_0 = B_50
      | k1_xboole_0 = A_49 ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_443,plain,
    ( k1_mcart_1('#skF_3') != '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_26,c_422])).

tff(c_448,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_443])).

tff(c_449,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_448])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_74,plain,(
    ! [B_29,A_30] :
      ( ~ r1_xboole_0(B_29,A_30)
      | ~ r1_tarski(B_29,A_30)
      | v1_xboole_0(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_77,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_74])).

tff(c_80,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_77])).

tff(c_38,plain,(
    ! [A_19,B_20] :
      ( v1_xboole_0(k2_zfmisc_1(A_19,B_20))
      | ~ v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_14,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_42,plain,(
    ! [A_19,B_20] :
      ( k2_zfmisc_1(A_19,B_20) = k1_xboole_0
      | ~ v1_xboole_0(A_19) ) ),
    inference(resolution,[status(thm)],[c_38,c_14])).

tff(c_89,plain,(
    ! [B_20] : k2_zfmisc_1(k1_xboole_0,B_20) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_80,c_42])).

tff(c_455,plain,(
    ! [B_20] : k2_zfmisc_1('#skF_1',B_20) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_449,c_449,c_89])).

tff(c_28,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_463,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_449,c_28])).

tff(c_492,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_455,c_463])).

tff(c_493,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_448])).

tff(c_48,plain,(
    ! [A_21,B_22] :
      ( v1_xboole_0(k2_zfmisc_1(A_21,B_22))
      | ~ v1_xboole_0(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_52,plain,(
    ! [A_21,B_22] :
      ( k2_zfmisc_1(A_21,B_22) = k1_xboole_0
      | ~ v1_xboole_0(B_22) ) ),
    inference(resolution,[status(thm)],[c_48,c_14])).

tff(c_88,plain,(
    ! [A_21] : k2_zfmisc_1(A_21,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_80,c_52])).

tff(c_502,plain,(
    ! [A_21] : k2_zfmisc_1(A_21,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_493,c_493,c_88])).

tff(c_509,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_493,c_28])).

tff(c_560,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_502,c_509])).

tff(c_561,plain,(
    k2_mcart_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_825,plain,(
    ! [C_76,A_77,B_78] :
      ( k2_mcart_1(C_76) != C_76
      | ~ m1_subset_1(C_76,k2_zfmisc_1(A_77,B_78))
      | k1_xboole_0 = B_78
      | k1_xboole_0 = A_77 ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_843,plain,
    ( k2_mcart_1('#skF_3') != '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_26,c_825])).

tff(c_848,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_561,c_843])).

tff(c_849,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_848])).

tff(c_572,plain,(
    ! [B_57,A_58] :
      ( ~ r1_xboole_0(B_57,A_58)
      | ~ r1_tarski(B_57,A_58)
      | v1_xboole_0(B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_575,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_572])).

tff(c_578,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_575])).

tff(c_617,plain,(
    ! [A_64,B_65] :
      ( k2_zfmisc_1(A_64,B_65) = k1_xboole_0
      | ~ v1_xboole_0(A_64) ) ),
    inference(resolution,[status(thm)],[c_38,c_14])).

tff(c_624,plain,(
    ! [B_65] : k2_zfmisc_1(k1_xboole_0,B_65) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_578,c_617])).

tff(c_854,plain,(
    ! [B_65] : k2_zfmisc_1('#skF_1',B_65) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_849,c_849,c_624])).

tff(c_861,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_849,c_28])).

tff(c_890,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_854,c_861])).

tff(c_891,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_848])).

tff(c_567,plain,(
    ! [A_55,B_56] :
      ( v1_xboole_0(k2_zfmisc_1(A_55,B_56))
      | ~ v1_xboole_0(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_584,plain,(
    ! [A_59,B_60] :
      ( k2_zfmisc_1(A_59,B_60) = k1_xboole_0
      | ~ v1_xboole_0(B_60) ) ),
    inference(resolution,[status(thm)],[c_567,c_14])).

tff(c_591,plain,(
    ! [A_59] : k2_zfmisc_1(A_59,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_578,c_584])).

tff(c_899,plain,(
    ! [A_59] : k2_zfmisc_1(A_59,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_891,c_891,c_591])).

tff(c_904,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_891,c_28])).

tff(c_961,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_899,c_904])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n001.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 16:17:45 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.45/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.31  
% 2.45/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.31  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.45/1.31  
% 2.45/1.31  %Foreground sorts:
% 2.45/1.31  
% 2.45/1.31  
% 2.45/1.31  %Background operators:
% 2.45/1.31  
% 2.45/1.31  
% 2.45/1.31  %Foreground operators:
% 2.45/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.45/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.45/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.45/1.31  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.45/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.45/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.45/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.45/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.45/1.31  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.45/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.45/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.45/1.31  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.45/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.45/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.45/1.31  
% 2.45/1.33  tff(f_93, negated_conjecture, ~(![A, B]: (~(k2_zfmisc_1(A, B) = k1_xboole_0) => (![C]: (m1_subset_1(C, k2_zfmisc_1(A, B)) => (~(C = k1_mcart_1(C)) & ~(C = k2_mcart_1(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_mcart_1)).
% 2.45/1.33  tff(f_80, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(![C]: (m1_subset_1(C, k2_zfmisc_1(A, B)) => (~(C = k1_mcart_1(C)) & ~(C = k2_mcart_1(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_mcart_1)).
% 2.45/1.33  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.45/1.33  tff(f_43, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.45/1.33  tff(f_51, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.45/1.33  tff(f_63, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 2.45/1.33  tff(f_55, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_boole)).
% 2.45/1.33  tff(f_59, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 2.45/1.33  tff(c_24, plain, (k2_mcart_1('#skF_3')='#skF_3' | k1_mcart_1('#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.45/1.33  tff(c_43, plain, (k1_mcart_1('#skF_3')='#skF_3'), inference(splitLeft, [status(thm)], [c_24])).
% 2.45/1.33  tff(c_26, plain, (m1_subset_1('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.45/1.33  tff(c_422, plain, (![C_48, A_49, B_50]: (k1_mcart_1(C_48)!=C_48 | ~m1_subset_1(C_48, k2_zfmisc_1(A_49, B_50)) | k1_xboole_0=B_50 | k1_xboole_0=A_49)), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.45/1.33  tff(c_443, plain, (k1_mcart_1('#skF_3')!='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_26, c_422])).
% 2.45/1.33  tff(c_448, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_43, c_443])).
% 2.45/1.33  tff(c_449, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_448])).
% 2.45/1.33  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.45/1.33  tff(c_8, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.45/1.33  tff(c_74, plain, (![B_29, A_30]: (~r1_xboole_0(B_29, A_30) | ~r1_tarski(B_29, A_30) | v1_xboole_0(B_29))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.45/1.33  tff(c_77, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0) | v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_74])).
% 2.45/1.33  tff(c_80, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_77])).
% 2.45/1.33  tff(c_38, plain, (![A_19, B_20]: (v1_xboole_0(k2_zfmisc_1(A_19, B_20)) | ~v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.45/1.33  tff(c_14, plain, (![A_6]: (k1_xboole_0=A_6 | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.45/1.33  tff(c_42, plain, (![A_19, B_20]: (k2_zfmisc_1(A_19, B_20)=k1_xboole_0 | ~v1_xboole_0(A_19))), inference(resolution, [status(thm)], [c_38, c_14])).
% 2.45/1.33  tff(c_89, plain, (![B_20]: (k2_zfmisc_1(k1_xboole_0, B_20)=k1_xboole_0)), inference(resolution, [status(thm)], [c_80, c_42])).
% 2.45/1.33  tff(c_455, plain, (![B_20]: (k2_zfmisc_1('#skF_1', B_20)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_449, c_449, c_89])).
% 2.45/1.33  tff(c_28, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.45/1.33  tff(c_463, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_449, c_28])).
% 2.45/1.33  tff(c_492, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_455, c_463])).
% 2.45/1.33  tff(c_493, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_448])).
% 2.45/1.33  tff(c_48, plain, (![A_21, B_22]: (v1_xboole_0(k2_zfmisc_1(A_21, B_22)) | ~v1_xboole_0(B_22))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.45/1.33  tff(c_52, plain, (![A_21, B_22]: (k2_zfmisc_1(A_21, B_22)=k1_xboole_0 | ~v1_xboole_0(B_22))), inference(resolution, [status(thm)], [c_48, c_14])).
% 2.45/1.33  tff(c_88, plain, (![A_21]: (k2_zfmisc_1(A_21, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_80, c_52])).
% 2.45/1.33  tff(c_502, plain, (![A_21]: (k2_zfmisc_1(A_21, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_493, c_493, c_88])).
% 2.45/1.33  tff(c_509, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_493, c_28])).
% 2.45/1.33  tff(c_560, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_502, c_509])).
% 2.45/1.33  tff(c_561, plain, (k2_mcart_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_24])).
% 2.45/1.33  tff(c_825, plain, (![C_76, A_77, B_78]: (k2_mcart_1(C_76)!=C_76 | ~m1_subset_1(C_76, k2_zfmisc_1(A_77, B_78)) | k1_xboole_0=B_78 | k1_xboole_0=A_77)), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.45/1.33  tff(c_843, plain, (k2_mcart_1('#skF_3')!='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_26, c_825])).
% 2.45/1.33  tff(c_848, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_561, c_843])).
% 2.45/1.33  tff(c_849, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_848])).
% 2.45/1.33  tff(c_572, plain, (![B_57, A_58]: (~r1_xboole_0(B_57, A_58) | ~r1_tarski(B_57, A_58) | v1_xboole_0(B_57))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.45/1.33  tff(c_575, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0) | v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_572])).
% 2.45/1.33  tff(c_578, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_575])).
% 2.45/1.33  tff(c_617, plain, (![A_64, B_65]: (k2_zfmisc_1(A_64, B_65)=k1_xboole_0 | ~v1_xboole_0(A_64))), inference(resolution, [status(thm)], [c_38, c_14])).
% 2.45/1.33  tff(c_624, plain, (![B_65]: (k2_zfmisc_1(k1_xboole_0, B_65)=k1_xboole_0)), inference(resolution, [status(thm)], [c_578, c_617])).
% 2.45/1.33  tff(c_854, plain, (![B_65]: (k2_zfmisc_1('#skF_1', B_65)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_849, c_849, c_624])).
% 2.45/1.33  tff(c_861, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_849, c_28])).
% 2.45/1.33  tff(c_890, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_854, c_861])).
% 2.45/1.33  tff(c_891, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_848])).
% 2.45/1.33  tff(c_567, plain, (![A_55, B_56]: (v1_xboole_0(k2_zfmisc_1(A_55, B_56)) | ~v1_xboole_0(B_56))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.45/1.33  tff(c_584, plain, (![A_59, B_60]: (k2_zfmisc_1(A_59, B_60)=k1_xboole_0 | ~v1_xboole_0(B_60))), inference(resolution, [status(thm)], [c_567, c_14])).
% 2.45/1.33  tff(c_591, plain, (![A_59]: (k2_zfmisc_1(A_59, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_578, c_584])).
% 2.45/1.33  tff(c_899, plain, (![A_59]: (k2_zfmisc_1(A_59, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_891, c_891, c_591])).
% 2.45/1.33  tff(c_904, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_891, c_28])).
% 2.45/1.33  tff(c_961, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_899, c_904])).
% 2.45/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.33  
% 2.45/1.33  Inference rules
% 2.45/1.33  ----------------------
% 2.45/1.33  #Ref     : 0
% 2.45/1.33  #Sup     : 207
% 2.45/1.33  #Fact    : 0
% 2.45/1.33  #Define  : 0
% 2.45/1.33  #Split   : 4
% 2.45/1.33  #Chain   : 0
% 2.45/1.33  #Close   : 0
% 2.45/1.33  
% 2.45/1.33  Ordering : KBO
% 2.45/1.33  
% 2.45/1.33  Simplification rules
% 2.45/1.33  ----------------------
% 2.45/1.33  #Subsume      : 12
% 2.45/1.33  #Demod        : 186
% 2.45/1.33  #Tautology    : 168
% 2.45/1.33  #SimpNegUnit  : 1
% 2.45/1.33  #BackRed      : 65
% 2.45/1.33  
% 2.45/1.33  #Partial instantiations: 0
% 2.45/1.33  #Strategies tried      : 1
% 2.45/1.33  
% 2.45/1.33  Timing (in seconds)
% 2.45/1.33  ----------------------
% 2.45/1.33  Preprocessing        : 0.27
% 2.45/1.33  Parsing              : 0.15
% 2.45/1.33  CNF conversion       : 0.02
% 2.45/1.33  Main loop            : 0.30
% 2.45/1.33  Inferencing          : 0.11
% 2.45/1.33  Reduction            : 0.09
% 2.45/1.33  Demodulation         : 0.06
% 2.45/1.33  BG Simplification    : 0.02
% 2.45/1.33  Subsumption          : 0.06
% 2.45/1.33  Abstraction          : 0.02
% 2.45/1.33  MUC search           : 0.00
% 2.45/1.33  Cooper               : 0.00
% 2.45/1.33  Total                : 0.61
% 2.45/1.33  Index Insertion      : 0.00
% 2.45/1.33  Index Deletion       : 0.00
% 2.45/1.33  Index Matching       : 0.00
% 2.45/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
