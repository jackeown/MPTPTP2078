%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:46 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :   61 (  85 expanded)
%              Number of leaves         :   24 (  38 expanded)
%              Depth                    :   11
%              Number of atoms          :  100 ( 164 expanded)
%              Number of equality atoms :   29 (  45 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k7_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

tff(f_43,axiom,(
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

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_67,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_36,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3')
    | k7_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_88,plain,(
    k7_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_34,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_146,plain,(
    ! [A_39,B_40,C_41] :
      ( r2_hidden(A_39,B_40)
      | ~ r2_hidden(A_39,k1_relat_1(k7_relat_1(C_41,B_40)))
      | ~ v1_relat_1(C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_161,plain,(
    ! [C_41,B_40] :
      ( r2_hidden('#skF_2'(k1_relat_1(k7_relat_1(C_41,B_40))),B_40)
      | ~ v1_relat_1(C_41)
      | k1_relat_1(k7_relat_1(C_41,B_40)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_146])).

tff(c_198,plain,(
    ! [A_49,C_50,B_51] :
      ( r2_hidden(A_49,k1_relat_1(C_50))
      | ~ r2_hidden(A_49,k1_relat_1(k7_relat_1(C_50,B_51)))
      | ~ v1_relat_1(C_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_458,plain,(
    ! [C_61,B_62] :
      ( r2_hidden('#skF_2'(k1_relat_1(k7_relat_1(C_61,B_62))),k1_relat_1(C_61))
      | ~ v1_relat_1(C_61)
      | k1_relat_1(k7_relat_1(C_61,B_62)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_198])).

tff(c_42,plain,
    ( k7_relat_1('#skF_4','#skF_3') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_121,plain,(
    r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_42])).

tff(c_136,plain,(
    ! [A_36,B_37,C_38] :
      ( ~ r1_xboole_0(A_36,B_37)
      | ~ r2_hidden(C_38,B_37)
      | ~ r2_hidden(C_38,A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_145,plain,(
    ! [C_38] :
      ( ~ r2_hidden(C_38,'#skF_3')
      | ~ r2_hidden(C_38,k1_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_121,c_136])).

tff(c_466,plain,(
    ! [B_62] :
      ( ~ r2_hidden('#skF_2'(k1_relat_1(k7_relat_1('#skF_4',B_62))),'#skF_3')
      | ~ v1_relat_1('#skF_4')
      | k1_relat_1(k7_relat_1('#skF_4',B_62)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_458,c_145])).

tff(c_761,plain,(
    ! [B_75] :
      ( ~ r2_hidden('#skF_2'(k1_relat_1(k7_relat_1('#skF_4',B_75))),'#skF_3')
      | k1_relat_1(k7_relat_1('#skF_4',B_75)) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_466])).

tff(c_772,plain,
    ( ~ v1_relat_1('#skF_4')
    | k1_relat_1(k7_relat_1('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_161,c_761])).

tff(c_778,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_772])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( v1_relat_1(k7_relat_1(A_12,B_13))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_90,plain,(
    ! [A_26] :
      ( k1_relat_1(A_26) != k1_xboole_0
      | k1_xboole_0 = A_26
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_97,plain,(
    ! [A_12,B_13] :
      ( k1_relat_1(k7_relat_1(A_12,B_13)) != k1_xboole_0
      | k7_relat_1(A_12,B_13) = k1_xboole_0
      | ~ v1_relat_1(A_12) ) ),
    inference(resolution,[status(thm)],[c_18,c_90])).

tff(c_806,plain,
    ( k7_relat_1('#skF_4','#skF_3') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_778,c_97])).

tff(c_829,plain,(
    k7_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_806])).

tff(c_831,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_829])).

tff(c_832,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_73,plain,(
    ! [A_20,B_21] : ~ r2_hidden(A_20,k2_zfmisc_1(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_76,plain,(
    ! [A_8] : ~ r2_hidden(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_73])).

tff(c_22,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_833,plain,(
    k7_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_966,plain,(
    ! [A_101,C_102,B_103] :
      ( r2_hidden(A_101,k1_relat_1(k7_relat_1(C_102,B_103)))
      | ~ r2_hidden(A_101,k1_relat_1(C_102))
      | ~ r2_hidden(A_101,B_103)
      | ~ v1_relat_1(C_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_975,plain,(
    ! [A_101] :
      ( r2_hidden(A_101,k1_relat_1(k1_xboole_0))
      | ~ r2_hidden(A_101,k1_relat_1('#skF_4'))
      | ~ r2_hidden(A_101,'#skF_3')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_833,c_966])).

tff(c_979,plain,(
    ! [A_101] :
      ( r2_hidden(A_101,k1_xboole_0)
      | ~ r2_hidden(A_101,k1_relat_1('#skF_4'))
      | ~ r2_hidden(A_101,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_22,c_975])).

tff(c_981,plain,(
    ! [A_104] :
      ( ~ r2_hidden(A_104,k1_relat_1('#skF_4'))
      | ~ r2_hidden(A_104,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_979])).

tff(c_999,plain,(
    ! [B_105] :
      ( ~ r2_hidden('#skF_1'(k1_relat_1('#skF_4'),B_105),'#skF_3')
      | r1_xboole_0(k1_relat_1('#skF_4'),B_105) ) ),
    inference(resolution,[status(thm)],[c_6,c_981])).

tff(c_1003,plain,(
    r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_999])).

tff(c_1007,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_832,c_832,c_1003])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:49:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.14/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.47  
% 3.14/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.48  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.14/1.48  
% 3.14/1.48  %Foreground sorts:
% 3.14/1.48  
% 3.14/1.48  
% 3.14/1.48  %Background operators:
% 3.14/1.48  
% 3.14/1.48  
% 3.14/1.48  %Foreground operators:
% 3.14/1.48  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.14/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.14/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.14/1.48  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.14/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.14/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.14/1.48  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.14/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.14/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.14/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.14/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.14/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.14/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.14/1.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.14/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.14/1.48  
% 3.14/1.49  tff(f_90, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 3.14/1.49  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.14/1.49  tff(f_83, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_relat_1)).
% 3.14/1.49  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.14/1.49  tff(f_64, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 3.14/1.49  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 3.14/1.49  tff(f_57, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.14/1.49  tff(f_60, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 3.14/1.49  tff(f_67, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.14/1.49  tff(c_36, plain, (~r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3') | k7_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.14/1.49  tff(c_88, plain, (k7_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_36])).
% 3.14/1.49  tff(c_34, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.14/1.49  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.14/1.49  tff(c_146, plain, (![A_39, B_40, C_41]: (r2_hidden(A_39, B_40) | ~r2_hidden(A_39, k1_relat_1(k7_relat_1(C_41, B_40))) | ~v1_relat_1(C_41))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.14/1.49  tff(c_161, plain, (![C_41, B_40]: (r2_hidden('#skF_2'(k1_relat_1(k7_relat_1(C_41, B_40))), B_40) | ~v1_relat_1(C_41) | k1_relat_1(k7_relat_1(C_41, B_40))=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_146])).
% 3.14/1.49  tff(c_198, plain, (![A_49, C_50, B_51]: (r2_hidden(A_49, k1_relat_1(C_50)) | ~r2_hidden(A_49, k1_relat_1(k7_relat_1(C_50, B_51))) | ~v1_relat_1(C_50))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.14/1.49  tff(c_458, plain, (![C_61, B_62]: (r2_hidden('#skF_2'(k1_relat_1(k7_relat_1(C_61, B_62))), k1_relat_1(C_61)) | ~v1_relat_1(C_61) | k1_relat_1(k7_relat_1(C_61, B_62))=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_198])).
% 3.14/1.49  tff(c_42, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.14/1.49  tff(c_121, plain, (r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_88, c_42])).
% 3.14/1.49  tff(c_136, plain, (![A_36, B_37, C_38]: (~r1_xboole_0(A_36, B_37) | ~r2_hidden(C_38, B_37) | ~r2_hidden(C_38, A_36))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.14/1.49  tff(c_145, plain, (![C_38]: (~r2_hidden(C_38, '#skF_3') | ~r2_hidden(C_38, k1_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_121, c_136])).
% 3.14/1.49  tff(c_466, plain, (![B_62]: (~r2_hidden('#skF_2'(k1_relat_1(k7_relat_1('#skF_4', B_62))), '#skF_3') | ~v1_relat_1('#skF_4') | k1_relat_1(k7_relat_1('#skF_4', B_62))=k1_xboole_0)), inference(resolution, [status(thm)], [c_458, c_145])).
% 3.14/1.49  tff(c_761, plain, (![B_75]: (~r2_hidden('#skF_2'(k1_relat_1(k7_relat_1('#skF_4', B_75))), '#skF_3') | k1_relat_1(k7_relat_1('#skF_4', B_75))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_466])).
% 3.14/1.49  tff(c_772, plain, (~v1_relat_1('#skF_4') | k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_161, c_761])).
% 3.14/1.49  tff(c_778, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_772])).
% 3.14/1.49  tff(c_18, plain, (![A_12, B_13]: (v1_relat_1(k7_relat_1(A_12, B_13)) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.14/1.49  tff(c_90, plain, (![A_26]: (k1_relat_1(A_26)!=k1_xboole_0 | k1_xboole_0=A_26 | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.14/1.49  tff(c_97, plain, (![A_12, B_13]: (k1_relat_1(k7_relat_1(A_12, B_13))!=k1_xboole_0 | k7_relat_1(A_12, B_13)=k1_xboole_0 | ~v1_relat_1(A_12))), inference(resolution, [status(thm)], [c_18, c_90])).
% 3.14/1.49  tff(c_806, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_778, c_97])).
% 3.14/1.49  tff(c_829, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_806])).
% 3.14/1.49  tff(c_831, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_829])).
% 3.14/1.49  tff(c_832, plain, (~r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_36])).
% 3.14/1.49  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.14/1.49  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.14/1.49  tff(c_12, plain, (![A_8]: (k2_zfmisc_1(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.14/1.49  tff(c_73, plain, (![A_20, B_21]: (~r2_hidden(A_20, k2_zfmisc_1(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.14/1.49  tff(c_76, plain, (![A_8]: (~r2_hidden(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_73])).
% 3.14/1.49  tff(c_22, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.14/1.49  tff(c_833, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 3.14/1.49  tff(c_966, plain, (![A_101, C_102, B_103]: (r2_hidden(A_101, k1_relat_1(k7_relat_1(C_102, B_103))) | ~r2_hidden(A_101, k1_relat_1(C_102)) | ~r2_hidden(A_101, B_103) | ~v1_relat_1(C_102))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.14/1.49  tff(c_975, plain, (![A_101]: (r2_hidden(A_101, k1_relat_1(k1_xboole_0)) | ~r2_hidden(A_101, k1_relat_1('#skF_4')) | ~r2_hidden(A_101, '#skF_3') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_833, c_966])).
% 3.14/1.49  tff(c_979, plain, (![A_101]: (r2_hidden(A_101, k1_xboole_0) | ~r2_hidden(A_101, k1_relat_1('#skF_4')) | ~r2_hidden(A_101, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_22, c_975])).
% 3.14/1.49  tff(c_981, plain, (![A_104]: (~r2_hidden(A_104, k1_relat_1('#skF_4')) | ~r2_hidden(A_104, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_76, c_979])).
% 3.14/1.49  tff(c_999, plain, (![B_105]: (~r2_hidden('#skF_1'(k1_relat_1('#skF_4'), B_105), '#skF_3') | r1_xboole_0(k1_relat_1('#skF_4'), B_105))), inference(resolution, [status(thm)], [c_6, c_981])).
% 3.14/1.49  tff(c_1003, plain, (r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_4, c_999])).
% 3.14/1.49  tff(c_1007, plain, $false, inference(negUnitSimplification, [status(thm)], [c_832, c_832, c_1003])).
% 3.14/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.49  
% 3.14/1.49  Inference rules
% 3.14/1.49  ----------------------
% 3.14/1.49  #Ref     : 0
% 3.14/1.49  #Sup     : 196
% 3.14/1.49  #Fact    : 0
% 3.14/1.49  #Define  : 0
% 3.14/1.49  #Split   : 5
% 3.14/1.49  #Chain   : 0
% 3.14/1.49  #Close   : 0
% 3.14/1.49  
% 3.14/1.49  Ordering : KBO
% 3.14/1.49  
% 3.14/1.49  Simplification rules
% 3.14/1.49  ----------------------
% 3.14/1.49  #Subsume      : 42
% 3.14/1.49  #Demod        : 189
% 3.14/1.49  #Tautology    : 91
% 3.14/1.49  #SimpNegUnit  : 35
% 3.14/1.49  #BackRed      : 1
% 3.14/1.49  
% 3.14/1.49  #Partial instantiations: 0
% 3.14/1.49  #Strategies tried      : 1
% 3.14/1.49  
% 3.14/1.49  Timing (in seconds)
% 3.14/1.49  ----------------------
% 3.14/1.49  Preprocessing        : 0.31
% 3.14/1.49  Parsing              : 0.17
% 3.14/1.49  CNF conversion       : 0.02
% 3.14/1.49  Main loop            : 0.36
% 3.14/1.49  Inferencing          : 0.14
% 3.14/1.49  Reduction            : 0.11
% 3.14/1.49  Demodulation         : 0.07
% 3.14/1.49  BG Simplification    : 0.02
% 3.14/1.49  Subsumption          : 0.07
% 3.14/1.49  Abstraction          : 0.02
% 3.14/1.49  MUC search           : 0.00
% 3.14/1.49  Cooper               : 0.00
% 3.14/1.49  Total                : 0.71
% 3.14/1.49  Index Insertion      : 0.00
% 3.14/1.49  Index Deletion       : 0.00
% 3.14/1.49  Index Matching       : 0.00
% 3.14/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
