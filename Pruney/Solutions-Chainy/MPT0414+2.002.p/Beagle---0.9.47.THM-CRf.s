%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:42 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 256 expanded)
%              Number of leaves         :   21 (  94 expanded)
%              Depth                    :   15
%              Number of atoms          :  117 ( 629 expanded)
%              Number of equality atoms :    7 (  51 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_82,negated_conjecture,(
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

tff(f_61,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_45,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_38,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_40,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_34,plain,(
    ! [A_15] : ~ v1_xboole_0(k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_110,plain,(
    ! [A_42,B_43] :
      ( r2_hidden(A_42,B_43)
      | v1_xboole_0(B_43)
      | ~ m1_subset_1(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_14,plain,(
    ! [C_12,A_8] :
      ( r1_tarski(C_12,A_8)
      | ~ r2_hidden(C_12,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_117,plain,(
    ! [A_42,A_8] :
      ( r1_tarski(A_42,A_8)
      | v1_xboole_0(k1_zfmisc_1(A_8))
      | ~ m1_subset_1(A_42,k1_zfmisc_1(A_8)) ) ),
    inference(resolution,[status(thm)],[c_110,c_14])).

tff(c_139,plain,(
    ! [A_46,A_47] :
      ( r1_tarski(A_46,A_47)
      | ~ m1_subset_1(A_46,k1_zfmisc_1(A_47)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_117])).

tff(c_155,plain,(
    r1_tarski('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_40,c_139])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_176,plain,(
    ! [C_49,B_50,A_51] :
      ( r2_hidden(C_49,B_50)
      | ~ r2_hidden(C_49,A_51)
      | ~ r1_tarski(A_51,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_333,plain,(
    ! [A_72,B_73,B_74] :
      ( r2_hidden('#skF_1'(A_72,B_73),B_74)
      | ~ r1_tarski(A_72,B_74)
      | r1_tarski(A_72,B_73) ) ),
    inference(resolution,[status(thm)],[c_6,c_176])).

tff(c_355,plain,(
    ! [A_72,B_73,A_8] :
      ( r1_tarski('#skF_1'(A_72,B_73),A_8)
      | ~ r1_tarski(A_72,k1_zfmisc_1(A_8))
      | r1_tarski(A_72,B_73) ) ),
    inference(resolution,[status(thm)],[c_333,c_14])).

tff(c_16,plain,(
    ! [C_12,A_8] :
      ( r2_hidden(C_12,k1_zfmisc_1(A_8))
      | ~ r1_tarski(C_12,A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_76,plain,(
    ! [B_34,A_35] :
      ( m1_subset_1(B_34,A_35)
      | ~ r2_hidden(B_34,A_35)
      | v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_79,plain,(
    ! [C_12,A_8] :
      ( m1_subset_1(C_12,k1_zfmisc_1(A_8))
      | v1_xboole_0(k1_zfmisc_1(A_8))
      | ~ r1_tarski(C_12,A_8) ) ),
    inference(resolution,[status(thm)],[c_16,c_76])).

tff(c_82,plain,(
    ! [C_12,A_8] :
      ( m1_subset_1(C_12,k1_zfmisc_1(A_8))
      | ~ r1_tarski(C_12,A_8) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_79])).

tff(c_163,plain,(
    ! [D_48] :
      ( r2_hidden(D_48,'#skF_5')
      | ~ r2_hidden(D_48,'#skF_6')
      | ~ m1_subset_1(D_48,k1_zfmisc_1('#skF_4')) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_215,plain,(
    ! [C_55] :
      ( r2_hidden(C_55,'#skF_5')
      | ~ r2_hidden(C_55,'#skF_6')
      | ~ r1_tarski(C_55,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_82,c_163])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_434,plain,(
    ! [A_87] :
      ( r1_tarski(A_87,'#skF_5')
      | ~ r2_hidden('#skF_1'(A_87,'#skF_5'),'#skF_6')
      | ~ r1_tarski('#skF_1'(A_87,'#skF_5'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_215,c_4])).

tff(c_449,plain,
    ( ~ r1_tarski('#skF_1'('#skF_6','#skF_5'),'#skF_4')
    | r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_434])).

tff(c_450,plain,(
    ~ r1_tarski('#skF_1'('#skF_6','#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_449])).

tff(c_476,plain,
    ( ~ r1_tarski('#skF_6',k1_zfmisc_1('#skF_4'))
    | r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_355,c_450])).

tff(c_479,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_476])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_483,plain,
    ( '#skF_5' = '#skF_6'
    | ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_479,c_8])).

tff(c_488,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_483])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_156,plain,(
    r1_tarski('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_42,c_139])).

tff(c_83,plain,(
    ! [C_36,A_37] :
      ( m1_subset_1(C_36,k1_zfmisc_1(A_37))
      | ~ r1_tarski(C_36,A_37) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_79])).

tff(c_46,plain,(
    ! [D_22] :
      ( r2_hidden(D_22,'#skF_6')
      | ~ r2_hidden(D_22,'#skF_5')
      | ~ m1_subset_1(D_22,k1_zfmisc_1('#skF_4')) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_199,plain,(
    ! [C_54] :
      ( r2_hidden(C_54,'#skF_6')
      | ~ r2_hidden(C_54,'#skF_5')
      | ~ r1_tarski(C_54,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_83,c_46])).

tff(c_451,plain,(
    ! [B_88] :
      ( r2_hidden('#skF_1'('#skF_5',B_88),'#skF_6')
      | ~ r1_tarski('#skF_1'('#skF_5',B_88),'#skF_4')
      | r1_tarski('#skF_5',B_88) ) ),
    inference(resolution,[status(thm)],[c_6,c_199])).

tff(c_471,plain,
    ( ~ r1_tarski('#skF_1'('#skF_5','#skF_6'),'#skF_4')
    | r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_451,c_4])).

tff(c_489,plain,(
    ~ r1_tarski('#skF_1'('#skF_5','#skF_6'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_488,c_471])).

tff(c_492,plain,
    ( ~ r1_tarski('#skF_5',k1_zfmisc_1('#skF_4'))
    | r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_355,c_489])).

tff(c_495,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_492])).

tff(c_497,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_488,c_495])).

tff(c_498,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_449])).

tff(c_503,plain,
    ( '#skF_5' = '#skF_6'
    | ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_498,c_8])).

tff(c_508,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_503])).

tff(c_535,plain,(
    ! [B_91] :
      ( r2_hidden('#skF_1'('#skF_5',B_91),'#skF_6')
      | ~ r1_tarski('#skF_1'('#skF_5',B_91),'#skF_4')
      | r1_tarski('#skF_5',B_91) ) ),
    inference(resolution,[status(thm)],[c_6,c_199])).

tff(c_547,plain,
    ( ~ r1_tarski('#skF_1'('#skF_5','#skF_6'),'#skF_4')
    | r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_535,c_4])).

tff(c_557,plain,(
    ~ r1_tarski('#skF_1'('#skF_5','#skF_6'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_508,c_508,c_547])).

tff(c_562,plain,
    ( ~ r1_tarski('#skF_5',k1_zfmisc_1('#skF_4'))
    | r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_355,c_557])).

tff(c_565,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_562])).

tff(c_567,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_508,c_565])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:45:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.38  
% 2.69/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.38  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 2.69/1.38  
% 2.69/1.38  %Foreground sorts:
% 2.69/1.38  
% 2.69/1.38  
% 2.69/1.38  %Background operators:
% 2.69/1.38  
% 2.69/1.38  
% 2.69/1.38  %Foreground operators:
% 2.69/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.69/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.69/1.38  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.69/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.69/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.69/1.38  tff('#skF_6', type, '#skF_6': $i).
% 2.69/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.69/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.69/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.69/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.69/1.38  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.69/1.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.69/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.69/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.69/1.38  
% 2.69/1.39  tff(f_82, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, B) <=> r2_hidden(D, C)))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_setfam_1)).
% 2.69/1.39  tff(f_61, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.69/1.39  tff(f_67, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.69/1.39  tff(f_45, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.69/1.39  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.69/1.39  tff(f_58, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.69/1.39  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.69/1.39  tff(c_38, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.69/1.39  tff(c_40, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k1_zfmisc_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.69/1.39  tff(c_34, plain, (![A_15]: (~v1_xboole_0(k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.69/1.39  tff(c_110, plain, (![A_42, B_43]: (r2_hidden(A_42, B_43) | v1_xboole_0(B_43) | ~m1_subset_1(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.69/1.39  tff(c_14, plain, (![C_12, A_8]: (r1_tarski(C_12, A_8) | ~r2_hidden(C_12, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.69/1.39  tff(c_117, plain, (![A_42, A_8]: (r1_tarski(A_42, A_8) | v1_xboole_0(k1_zfmisc_1(A_8)) | ~m1_subset_1(A_42, k1_zfmisc_1(A_8)))), inference(resolution, [status(thm)], [c_110, c_14])).
% 2.69/1.39  tff(c_139, plain, (![A_46, A_47]: (r1_tarski(A_46, A_47) | ~m1_subset_1(A_46, k1_zfmisc_1(A_47)))), inference(negUnitSimplification, [status(thm)], [c_34, c_117])).
% 2.69/1.39  tff(c_155, plain, (r1_tarski('#skF_6', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_139])).
% 2.69/1.39  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.69/1.39  tff(c_176, plain, (![C_49, B_50, A_51]: (r2_hidden(C_49, B_50) | ~r2_hidden(C_49, A_51) | ~r1_tarski(A_51, B_50))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.69/1.39  tff(c_333, plain, (![A_72, B_73, B_74]: (r2_hidden('#skF_1'(A_72, B_73), B_74) | ~r1_tarski(A_72, B_74) | r1_tarski(A_72, B_73))), inference(resolution, [status(thm)], [c_6, c_176])).
% 2.69/1.39  tff(c_355, plain, (![A_72, B_73, A_8]: (r1_tarski('#skF_1'(A_72, B_73), A_8) | ~r1_tarski(A_72, k1_zfmisc_1(A_8)) | r1_tarski(A_72, B_73))), inference(resolution, [status(thm)], [c_333, c_14])).
% 2.69/1.39  tff(c_16, plain, (![C_12, A_8]: (r2_hidden(C_12, k1_zfmisc_1(A_8)) | ~r1_tarski(C_12, A_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.69/1.39  tff(c_76, plain, (![B_34, A_35]: (m1_subset_1(B_34, A_35) | ~r2_hidden(B_34, A_35) | v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.69/1.39  tff(c_79, plain, (![C_12, A_8]: (m1_subset_1(C_12, k1_zfmisc_1(A_8)) | v1_xboole_0(k1_zfmisc_1(A_8)) | ~r1_tarski(C_12, A_8))), inference(resolution, [status(thm)], [c_16, c_76])).
% 2.69/1.39  tff(c_82, plain, (![C_12, A_8]: (m1_subset_1(C_12, k1_zfmisc_1(A_8)) | ~r1_tarski(C_12, A_8))), inference(negUnitSimplification, [status(thm)], [c_34, c_79])).
% 2.69/1.39  tff(c_163, plain, (![D_48]: (r2_hidden(D_48, '#skF_5') | ~r2_hidden(D_48, '#skF_6') | ~m1_subset_1(D_48, k1_zfmisc_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.69/1.39  tff(c_215, plain, (![C_55]: (r2_hidden(C_55, '#skF_5') | ~r2_hidden(C_55, '#skF_6') | ~r1_tarski(C_55, '#skF_4'))), inference(resolution, [status(thm)], [c_82, c_163])).
% 2.69/1.39  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.69/1.39  tff(c_434, plain, (![A_87]: (r1_tarski(A_87, '#skF_5') | ~r2_hidden('#skF_1'(A_87, '#skF_5'), '#skF_6') | ~r1_tarski('#skF_1'(A_87, '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_215, c_4])).
% 2.69/1.39  tff(c_449, plain, (~r1_tarski('#skF_1'('#skF_6', '#skF_5'), '#skF_4') | r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_6, c_434])).
% 2.69/1.39  tff(c_450, plain, (~r1_tarski('#skF_1'('#skF_6', '#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_449])).
% 2.69/1.39  tff(c_476, plain, (~r1_tarski('#skF_6', k1_zfmisc_1('#skF_4')) | r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_355, c_450])).
% 2.69/1.39  tff(c_479, plain, (r1_tarski('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_155, c_476])).
% 2.69/1.39  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.69/1.39  tff(c_483, plain, ('#skF_5'='#skF_6' | ~r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_479, c_8])).
% 2.69/1.39  tff(c_488, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_38, c_483])).
% 2.69/1.39  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.69/1.39  tff(c_156, plain, (r1_tarski('#skF_5', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_42, c_139])).
% 2.69/1.39  tff(c_83, plain, (![C_36, A_37]: (m1_subset_1(C_36, k1_zfmisc_1(A_37)) | ~r1_tarski(C_36, A_37))), inference(negUnitSimplification, [status(thm)], [c_34, c_79])).
% 2.69/1.39  tff(c_46, plain, (![D_22]: (r2_hidden(D_22, '#skF_6') | ~r2_hidden(D_22, '#skF_5') | ~m1_subset_1(D_22, k1_zfmisc_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.69/1.39  tff(c_199, plain, (![C_54]: (r2_hidden(C_54, '#skF_6') | ~r2_hidden(C_54, '#skF_5') | ~r1_tarski(C_54, '#skF_4'))), inference(resolution, [status(thm)], [c_83, c_46])).
% 2.69/1.39  tff(c_451, plain, (![B_88]: (r2_hidden('#skF_1'('#skF_5', B_88), '#skF_6') | ~r1_tarski('#skF_1'('#skF_5', B_88), '#skF_4') | r1_tarski('#skF_5', B_88))), inference(resolution, [status(thm)], [c_6, c_199])).
% 2.69/1.39  tff(c_471, plain, (~r1_tarski('#skF_1'('#skF_5', '#skF_6'), '#skF_4') | r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_451, c_4])).
% 2.69/1.39  tff(c_489, plain, (~r1_tarski('#skF_1'('#skF_5', '#skF_6'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_488, c_471])).
% 2.69/1.39  tff(c_492, plain, (~r1_tarski('#skF_5', k1_zfmisc_1('#skF_4')) | r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_355, c_489])).
% 2.69/1.39  tff(c_495, plain, (r1_tarski('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_156, c_492])).
% 2.69/1.39  tff(c_497, plain, $false, inference(negUnitSimplification, [status(thm)], [c_488, c_495])).
% 2.69/1.39  tff(c_498, plain, (r1_tarski('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_449])).
% 2.69/1.39  tff(c_503, plain, ('#skF_5'='#skF_6' | ~r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_498, c_8])).
% 2.69/1.39  tff(c_508, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_38, c_503])).
% 2.69/1.39  tff(c_535, plain, (![B_91]: (r2_hidden('#skF_1'('#skF_5', B_91), '#skF_6') | ~r1_tarski('#skF_1'('#skF_5', B_91), '#skF_4') | r1_tarski('#skF_5', B_91))), inference(resolution, [status(thm)], [c_6, c_199])).
% 2.69/1.39  tff(c_547, plain, (~r1_tarski('#skF_1'('#skF_5', '#skF_6'), '#skF_4') | r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_535, c_4])).
% 2.69/1.39  tff(c_557, plain, (~r1_tarski('#skF_1'('#skF_5', '#skF_6'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_508, c_508, c_547])).
% 2.69/1.39  tff(c_562, plain, (~r1_tarski('#skF_5', k1_zfmisc_1('#skF_4')) | r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_355, c_557])).
% 2.69/1.39  tff(c_565, plain, (r1_tarski('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_156, c_562])).
% 2.69/1.39  tff(c_567, plain, $false, inference(negUnitSimplification, [status(thm)], [c_508, c_565])).
% 2.69/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.39  
% 2.69/1.39  Inference rules
% 2.69/1.39  ----------------------
% 2.69/1.39  #Ref     : 0
% 2.69/1.39  #Sup     : 103
% 2.69/1.39  #Fact    : 0
% 2.69/1.39  #Define  : 0
% 2.69/1.39  #Split   : 6
% 2.69/1.39  #Chain   : 0
% 2.69/1.39  #Close   : 0
% 2.69/1.39  
% 2.69/1.39  Ordering : KBO
% 2.69/1.39  
% 2.69/1.39  Simplification rules
% 2.69/1.39  ----------------------
% 2.69/1.39  #Subsume      : 14
% 2.69/1.39  #Demod        : 19
% 2.69/1.39  #Tautology    : 27
% 2.69/1.39  #SimpNegUnit  : 16
% 2.69/1.39  #BackRed      : 0
% 2.69/1.39  
% 2.69/1.39  #Partial instantiations: 0
% 2.69/1.39  #Strategies tried      : 1
% 2.69/1.39  
% 2.69/1.39  Timing (in seconds)
% 2.69/1.39  ----------------------
% 2.69/1.40  Preprocessing        : 0.30
% 2.69/1.40  Parsing              : 0.16
% 2.69/1.40  CNF conversion       : 0.02
% 2.69/1.40  Main loop            : 0.32
% 2.69/1.40  Inferencing          : 0.12
% 3.00/1.40  Reduction            : 0.09
% 3.00/1.40  Demodulation         : 0.06
% 3.00/1.40  BG Simplification    : 0.02
% 3.00/1.40  Subsumption          : 0.08
% 3.00/1.40  Abstraction          : 0.01
% 3.00/1.40  MUC search           : 0.00
% 3.00/1.40  Cooper               : 0.00
% 3.00/1.40  Total                : 0.65
% 3.00/1.40  Index Insertion      : 0.00
% 3.00/1.40  Index Deletion       : 0.00
% 3.00/1.40  Index Matching       : 0.00
% 3.00/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
