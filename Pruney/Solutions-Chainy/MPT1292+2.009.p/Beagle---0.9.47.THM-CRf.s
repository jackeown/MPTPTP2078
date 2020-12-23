%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:30 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 126 expanded)
%              Number of leaves         :   29 (  56 expanded)
%              Depth                    :   16
%              Number of atoms          :   90 ( 257 expanded)
%              Number of equality atoms :   31 (  94 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(m1_setfam_1,type,(
    m1_setfam_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_95,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ~ ( m1_setfam_1(B,u1_struct_0(A))
                & B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_tops_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_81,axiom,(
    ! [A] :
      ( ~ ( ? [B] :
              ( B != k1_xboole_0
              & r2_hidden(B,A) )
          & k3_tarski(A) = k1_xboole_0 )
      & ~ ( k3_tarski(A) != k1_xboole_0
          & ! [B] :
              ~ ( B != k1_xboole_0
                & r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_orders_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_38,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_setfam_1(B,A)
    <=> r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).

tff(f_61,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_46,plain,(
    l1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_40,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_55,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2])).

tff(c_42,plain,(
    m1_setfam_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_10,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_53,plain,(
    ! [A_3] : r1_tarski('#skF_5',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_10])).

tff(c_36,plain,(
    ! [A_15] :
      ( r2_hidden('#skF_3'(A_15),A_15)
      | k3_tarski(A_15) = k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_50,plain,(
    ! [A_15] :
      ( r2_hidden('#skF_3'(A_15),A_15)
      | k3_tarski(A_15) = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36])).

tff(c_85,plain,(
    ! [C_25,A_26] :
      ( r1_tarski(C_25,A_26)
      | ~ r2_hidden(C_25,k1_zfmisc_1(A_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_201,plain,(
    ! [A_49] :
      ( r1_tarski('#skF_3'(k1_zfmisc_1(A_49)),A_49)
      | k3_tarski(k1_zfmisc_1(A_49)) = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_50,c_85])).

tff(c_12,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_52,plain,(
    ! [A_4] :
      ( A_4 = '#skF_5'
      | ~ r1_tarski(A_4,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40,c_12])).

tff(c_214,plain,
    ( '#skF_3'(k1_zfmisc_1('#skF_5')) = '#skF_5'
    | k3_tarski(k1_zfmisc_1('#skF_5')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_201,c_52])).

tff(c_215,plain,(
    k3_tarski(k1_zfmisc_1('#skF_5')) = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_214])).

tff(c_26,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(k3_tarski(A_10),k3_tarski(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_289,plain,(
    ! [A_54] :
      ( r1_tarski(k3_tarski(A_54),'#skF_5')
      | ~ r1_tarski(A_54,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_26])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_291,plain,(
    ! [A_54] :
      ( k3_tarski(A_54) = '#skF_5'
      | ~ r1_tarski('#skF_5',k3_tarski(A_54))
      | ~ r1_tarski(A_54,k1_zfmisc_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_289,c_4])).

tff(c_308,plain,(
    ! [A_55] :
      ( k3_tarski(A_55) = '#skF_5'
      | ~ r1_tarski(A_55,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_291])).

tff(c_324,plain,(
    k3_tarski('#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_53,c_308])).

tff(c_28,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,k3_tarski(B_13))
      | ~ m1_setfam_1(B_13,A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_373,plain,(
    ! [A_58] :
      ( r1_tarski(A_58,'#skF_5')
      | ~ m1_setfam_1('#skF_5',A_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_28])).

tff(c_379,plain,(
    ! [A_58] :
      ( A_58 = '#skF_5'
      | ~ r1_tarski('#skF_5',A_58)
      | ~ m1_setfam_1('#skF_5',A_58) ) ),
    inference(resolution,[status(thm)],[c_373,c_4])).

tff(c_388,plain,(
    ! [A_59] :
      ( A_59 = '#skF_5'
      | ~ m1_setfam_1('#skF_5',A_59) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_379])).

tff(c_409,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_42,c_388])).

tff(c_32,plain,(
    ! [A_14] :
      ( ~ v1_xboole_0(u1_struct_0(A_14))
      | ~ l1_struct_0(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_416,plain,
    ( ~ v1_xboole_0('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_32])).

tff(c_420,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_55,c_416])).

tff(c_422,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_420])).

tff(c_423,plain,(
    '#skF_3'(k1_zfmisc_1('#skF_5')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_214])).

tff(c_38,plain,(
    ! [A_15] :
      ( '#skF_3'(A_15) != k1_xboole_0
      | k3_tarski(A_15) = k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_49,plain,(
    ! [A_15] :
      ( '#skF_3'(A_15) != '#skF_5'
      | k3_tarski(A_15) = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40,c_38])).

tff(c_424,plain,(
    k3_tarski(k1_zfmisc_1('#skF_5')) != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_214])).

tff(c_438,plain,(
    '#skF_3'(k1_zfmisc_1('#skF_5')) != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_424])).

tff(c_442,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_423,c_438])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:48:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.36  
% 2.28/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.36  %$ r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 2.43/1.36  
% 2.43/1.36  %Foreground sorts:
% 2.43/1.36  
% 2.43/1.36  
% 2.43/1.36  %Background operators:
% 2.43/1.36  
% 2.43/1.36  
% 2.43/1.36  %Foreground operators:
% 2.43/1.36  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.43/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.43/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.43/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.43/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.43/1.36  tff('#skF_5', type, '#skF_5': $i).
% 2.43/1.36  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 2.43/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.43/1.36  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.43/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.43/1.36  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.43/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.43/1.36  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.43/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.43/1.36  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.43/1.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.43/1.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.43/1.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.43/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.43/1.36  
% 2.43/1.38  tff(f_95, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~(m1_setfam_1(B, u1_struct_0(A)) & (B = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_tops_2)).
% 2.43/1.38  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.43/1.38  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.43/1.38  tff(f_81, axiom, (![A]: (~((?[B]: (~(B = k1_xboole_0) & r2_hidden(B, A))) & (k3_tarski(A) = k1_xboole_0)) & ~(~(k3_tarski(A) = k1_xboole_0) & (![B]: ~(~(B = k1_xboole_0) & r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_orders_1)).
% 2.43/1.38  tff(f_45, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.43/1.38  tff(f_38, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.43/1.38  tff(f_49, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 2.43/1.38  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.43/1.38  tff(f_53, axiom, (![A, B]: (m1_setfam_1(B, A) <=> r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_setfam_1)).
% 2.43/1.38  tff(f_61, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.43/1.38  tff(c_48, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.43/1.38  tff(c_46, plain, (l1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.43/1.38  tff(c_40, plain, (k1_xboole_0='#skF_5'), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.43/1.38  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.43/1.38  tff(c_55, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2])).
% 2.43/1.38  tff(c_42, plain, (m1_setfam_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.43/1.38  tff(c_10, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.43/1.38  tff(c_53, plain, (![A_3]: (r1_tarski('#skF_5', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_10])).
% 2.43/1.38  tff(c_36, plain, (![A_15]: (r2_hidden('#skF_3'(A_15), A_15) | k3_tarski(A_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.43/1.38  tff(c_50, plain, (![A_15]: (r2_hidden('#skF_3'(A_15), A_15) | k3_tarski(A_15)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36])).
% 2.43/1.38  tff(c_85, plain, (![C_25, A_26]: (r1_tarski(C_25, A_26) | ~r2_hidden(C_25, k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.43/1.38  tff(c_201, plain, (![A_49]: (r1_tarski('#skF_3'(k1_zfmisc_1(A_49)), A_49) | k3_tarski(k1_zfmisc_1(A_49))='#skF_5')), inference(resolution, [status(thm)], [c_50, c_85])).
% 2.43/1.38  tff(c_12, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.43/1.38  tff(c_52, plain, (![A_4]: (A_4='#skF_5' | ~r1_tarski(A_4, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_40, c_12])).
% 2.43/1.38  tff(c_214, plain, ('#skF_3'(k1_zfmisc_1('#skF_5'))='#skF_5' | k3_tarski(k1_zfmisc_1('#skF_5'))='#skF_5'), inference(resolution, [status(thm)], [c_201, c_52])).
% 2.43/1.38  tff(c_215, plain, (k3_tarski(k1_zfmisc_1('#skF_5'))='#skF_5'), inference(splitLeft, [status(thm)], [c_214])).
% 2.43/1.38  tff(c_26, plain, (![A_10, B_11]: (r1_tarski(k3_tarski(A_10), k3_tarski(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.43/1.38  tff(c_289, plain, (![A_54]: (r1_tarski(k3_tarski(A_54), '#skF_5') | ~r1_tarski(A_54, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_215, c_26])).
% 2.43/1.38  tff(c_4, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.43/1.38  tff(c_291, plain, (![A_54]: (k3_tarski(A_54)='#skF_5' | ~r1_tarski('#skF_5', k3_tarski(A_54)) | ~r1_tarski(A_54, k1_zfmisc_1('#skF_5')))), inference(resolution, [status(thm)], [c_289, c_4])).
% 2.43/1.38  tff(c_308, plain, (![A_55]: (k3_tarski(A_55)='#skF_5' | ~r1_tarski(A_55, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_291])).
% 2.43/1.38  tff(c_324, plain, (k3_tarski('#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_53, c_308])).
% 2.43/1.38  tff(c_28, plain, (![A_12, B_13]: (r1_tarski(A_12, k3_tarski(B_13)) | ~m1_setfam_1(B_13, A_12))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.43/1.38  tff(c_373, plain, (![A_58]: (r1_tarski(A_58, '#skF_5') | ~m1_setfam_1('#skF_5', A_58))), inference(superposition, [status(thm), theory('equality')], [c_324, c_28])).
% 2.43/1.38  tff(c_379, plain, (![A_58]: (A_58='#skF_5' | ~r1_tarski('#skF_5', A_58) | ~m1_setfam_1('#skF_5', A_58))), inference(resolution, [status(thm)], [c_373, c_4])).
% 2.43/1.38  tff(c_388, plain, (![A_59]: (A_59='#skF_5' | ~m1_setfam_1('#skF_5', A_59))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_379])).
% 2.43/1.38  tff(c_409, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_42, c_388])).
% 2.43/1.38  tff(c_32, plain, (![A_14]: (~v1_xboole_0(u1_struct_0(A_14)) | ~l1_struct_0(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.43/1.38  tff(c_416, plain, (~v1_xboole_0('#skF_5') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_409, c_32])).
% 2.43/1.38  tff(c_420, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_55, c_416])).
% 2.43/1.38  tff(c_422, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_420])).
% 2.43/1.38  tff(c_423, plain, ('#skF_3'(k1_zfmisc_1('#skF_5'))='#skF_5'), inference(splitRight, [status(thm)], [c_214])).
% 2.43/1.38  tff(c_38, plain, (![A_15]: ('#skF_3'(A_15)!=k1_xboole_0 | k3_tarski(A_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.43/1.38  tff(c_49, plain, (![A_15]: ('#skF_3'(A_15)!='#skF_5' | k3_tarski(A_15)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_40, c_38])).
% 2.43/1.38  tff(c_424, plain, (k3_tarski(k1_zfmisc_1('#skF_5'))!='#skF_5'), inference(splitRight, [status(thm)], [c_214])).
% 2.43/1.38  tff(c_438, plain, ('#skF_3'(k1_zfmisc_1('#skF_5'))!='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_49, c_424])).
% 2.43/1.38  tff(c_442, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_423, c_438])).
% 2.43/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.38  
% 2.43/1.38  Inference rules
% 2.43/1.38  ----------------------
% 2.43/1.38  #Ref     : 0
% 2.43/1.38  #Sup     : 88
% 2.43/1.38  #Fact    : 0
% 2.43/1.38  #Define  : 0
% 2.43/1.38  #Split   : 2
% 2.43/1.38  #Chain   : 0
% 2.43/1.38  #Close   : 0
% 2.43/1.38  
% 2.43/1.38  Ordering : KBO
% 2.43/1.38  
% 2.43/1.38  Simplification rules
% 2.43/1.38  ----------------------
% 2.43/1.38  #Subsume      : 6
% 2.43/1.38  #Demod        : 46
% 2.43/1.38  #Tautology    : 44
% 2.43/1.38  #SimpNegUnit  : 1
% 2.43/1.38  #BackRed      : 2
% 2.43/1.38  
% 2.43/1.38  #Partial instantiations: 0
% 2.43/1.38  #Strategies tried      : 1
% 2.43/1.38  
% 2.43/1.38  Timing (in seconds)
% 2.43/1.38  ----------------------
% 2.43/1.38  Preprocessing        : 0.33
% 2.43/1.38  Parsing              : 0.18
% 2.43/1.38  CNF conversion       : 0.02
% 2.43/1.38  Main loop            : 0.23
% 2.43/1.38  Inferencing          : 0.08
% 2.43/1.38  Reduction            : 0.07
% 2.43/1.38  Demodulation         : 0.05
% 2.43/1.38  BG Simplification    : 0.01
% 2.43/1.38  Subsumption          : 0.05
% 2.43/1.38  Abstraction          : 0.01
% 2.43/1.38  MUC search           : 0.00
% 2.43/1.38  Cooper               : 0.00
% 2.43/1.38  Total                : 0.59
% 2.43/1.38  Index Insertion      : 0.00
% 2.43/1.38  Index Deletion       : 0.00
% 2.43/1.38  Index Matching       : 0.00
% 2.43/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
