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
% DateTime   : Thu Dec  3 10:00:50 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 152 expanded)
%              Number of leaves         :   22 (  60 expanded)
%              Depth                    :   10
%              Number of atoms          :   88 ( 245 expanded)
%              Number of equality atoms :   31 (  87 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k9_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_31,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_50,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_37,plain,(
    ! [A_9] :
      ( k1_xboole_0 = A_9
      | ~ v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_41,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_37])).

tff(c_18,plain,(
    ! [B_8,A_7] :
      ( r1_xboole_0(k1_relat_1(B_8),A_7)
      | k7_relat_1(B_8,A_7) != k1_xboole_0
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_159,plain,(
    ! [B_26,A_27] :
      ( r1_xboole_0(k1_relat_1(B_26),A_27)
      | k7_relat_1(B_26,A_27) != '#skF_1'
      | ~ v1_relat_1(B_26) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_18])).

tff(c_22,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2')
    | k9_relat_1('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_58,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2')
    | k9_relat_1('#skF_3','#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_22])).

tff(c_59,plain,(
    k9_relat_1('#skF_3','#skF_2') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_12,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_44,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_41,c_12])).

tff(c_28,plain,
    ( k9_relat_1('#skF_3','#skF_2') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_72,plain,
    ( k9_relat_1('#skF_3','#skF_2') = '#skF_1'
    | r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_28])).

tff(c_73,plain,(
    r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_72])).

tff(c_16,plain,(
    ! [B_8,A_7] :
      ( k7_relat_1(B_8,A_7) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_8),A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_93,plain,(
    ! [B_18,A_19] :
      ( k7_relat_1(B_18,A_19) = '#skF_1'
      | ~ r1_xboole_0(k1_relat_1(B_18),A_19)
      | ~ v1_relat_1(B_18) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_16])).

tff(c_99,plain,
    ( k7_relat_1('#skF_3','#skF_2') = '#skF_1'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_73,c_93])).

tff(c_106,plain,(
    k7_relat_1('#skF_3','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_99])).

tff(c_10,plain,(
    ! [B_6,A_5] :
      ( k2_relat_1(k7_relat_1(B_6,A_5)) = k9_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_110,plain,
    ( k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_10])).

tff(c_117,plain,(
    k9_relat_1('#skF_3','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_44,c_110])).

tff(c_119,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_117])).

tff(c_120,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_165,plain,
    ( k7_relat_1('#skF_3','#skF_2') != '#skF_1'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_159,c_120])).

tff(c_172,plain,(
    k7_relat_1('#skF_3','#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_165])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( v1_relat_1(k7_relat_1(A_2,B_3))
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_121,plain,(
    k9_relat_1('#skF_3','#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_140,plain,(
    ! [B_22,A_23] :
      ( k2_relat_1(k7_relat_1(B_22,A_23)) = k9_relat_1(B_22,A_23)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [A_4] :
      ( ~ v1_xboole_0(k2_relat_1(A_4))
      | ~ v1_relat_1(A_4)
      | v1_xboole_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_173,plain,(
    ! [B_28,A_29] :
      ( ~ v1_xboole_0(k9_relat_1(B_28,A_29))
      | ~ v1_relat_1(k7_relat_1(B_28,A_29))
      | v1_xboole_0(k7_relat_1(B_28,A_29))
      | ~ v1_relat_1(B_28) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_8])).

tff(c_176,plain,
    ( ~ v1_xboole_0('#skF_1')
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | v1_xboole_0(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_173])).

tff(c_178,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | v1_xboole_0(k7_relat_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_4,c_176])).

tff(c_179,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_178])).

tff(c_182,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_179])).

tff(c_186,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_182])).

tff(c_187,plain,(
    v1_xboole_0(k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_43,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_2])).

tff(c_191,plain,(
    k7_relat_1('#skF_3','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_187,c_43])).

tff(c_195,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_172,c_191])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 10:13:30 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.83/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.17  
% 1.83/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.17  %$ r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.83/1.17  
% 1.83/1.17  %Foreground sorts:
% 1.83/1.17  
% 1.83/1.17  
% 1.83/1.17  %Background operators:
% 1.83/1.17  
% 1.83/1.17  
% 1.83/1.17  %Foreground operators:
% 1.83/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.83/1.17  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.83/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.83/1.17  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.83/1.17  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.83/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.83/1.17  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.83/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.83/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.83/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.83/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.83/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.83/1.17  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.83/1.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.83/1.17  
% 1.83/1.18  tff(f_63, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 1.83/1.18  tff(f_31, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 1.83/1.18  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.83/1.18  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 1.83/1.18  tff(f_50, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.83/1.18  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 1.83/1.18  tff(f_35, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 1.83/1.18  tff(f_43, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 1.83/1.18  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.83/1.18  tff(c_4, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.83/1.18  tff(c_37, plain, (![A_9]: (k1_xboole_0=A_9 | ~v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.83/1.18  tff(c_41, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_4, c_37])).
% 1.83/1.18  tff(c_18, plain, (![B_8, A_7]: (r1_xboole_0(k1_relat_1(B_8), A_7) | k7_relat_1(B_8, A_7)!=k1_xboole_0 | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.83/1.18  tff(c_159, plain, (![B_26, A_27]: (r1_xboole_0(k1_relat_1(B_26), A_27) | k7_relat_1(B_26, A_27)!='#skF_1' | ~v1_relat_1(B_26))), inference(demodulation, [status(thm), theory('equality')], [c_41, c_18])).
% 1.83/1.18  tff(c_22, plain, (~r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2') | k9_relat_1('#skF_3', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.83/1.18  tff(c_58, plain, (~r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2') | k9_relat_1('#skF_3', '#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_41, c_22])).
% 1.83/1.18  tff(c_59, plain, (k9_relat_1('#skF_3', '#skF_2')!='#skF_1'), inference(splitLeft, [status(thm)], [c_58])).
% 1.83/1.18  tff(c_12, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.83/1.18  tff(c_44, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_41, c_41, c_12])).
% 1.83/1.18  tff(c_28, plain, (k9_relat_1('#skF_3', '#skF_2')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.83/1.18  tff(c_72, plain, (k9_relat_1('#skF_3', '#skF_2')='#skF_1' | r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_41, c_28])).
% 1.83/1.18  tff(c_73, plain, (r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_59, c_72])).
% 1.83/1.18  tff(c_16, plain, (![B_8, A_7]: (k7_relat_1(B_8, A_7)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_8), A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.83/1.18  tff(c_93, plain, (![B_18, A_19]: (k7_relat_1(B_18, A_19)='#skF_1' | ~r1_xboole_0(k1_relat_1(B_18), A_19) | ~v1_relat_1(B_18))), inference(demodulation, [status(thm), theory('equality')], [c_41, c_16])).
% 1.83/1.18  tff(c_99, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_1' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_73, c_93])).
% 1.83/1.18  tff(c_106, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_99])).
% 1.83/1.18  tff(c_10, plain, (![B_6, A_5]: (k2_relat_1(k7_relat_1(B_6, A_5))=k9_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.83/1.18  tff(c_110, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_106, c_10])).
% 1.83/1.18  tff(c_117, plain, (k9_relat_1('#skF_3', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_44, c_110])).
% 1.83/1.18  tff(c_119, plain, $false, inference(negUnitSimplification, [status(thm)], [c_59, c_117])).
% 1.83/1.18  tff(c_120, plain, (~r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_58])).
% 1.83/1.18  tff(c_165, plain, (k7_relat_1('#skF_3', '#skF_2')!='#skF_1' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_159, c_120])).
% 1.83/1.18  tff(c_172, plain, (k7_relat_1('#skF_3', '#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_165])).
% 1.83/1.18  tff(c_6, plain, (![A_2, B_3]: (v1_relat_1(k7_relat_1(A_2, B_3)) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.83/1.18  tff(c_121, plain, (k9_relat_1('#skF_3', '#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_58])).
% 1.83/1.18  tff(c_140, plain, (![B_22, A_23]: (k2_relat_1(k7_relat_1(B_22, A_23))=k9_relat_1(B_22, A_23) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.83/1.18  tff(c_8, plain, (![A_4]: (~v1_xboole_0(k2_relat_1(A_4)) | ~v1_relat_1(A_4) | v1_xboole_0(A_4))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.83/1.18  tff(c_173, plain, (![B_28, A_29]: (~v1_xboole_0(k9_relat_1(B_28, A_29)) | ~v1_relat_1(k7_relat_1(B_28, A_29)) | v1_xboole_0(k7_relat_1(B_28, A_29)) | ~v1_relat_1(B_28))), inference(superposition, [status(thm), theory('equality')], [c_140, c_8])).
% 1.83/1.18  tff(c_176, plain, (~v1_xboole_0('#skF_1') | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | v1_xboole_0(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_121, c_173])).
% 1.83/1.18  tff(c_178, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | v1_xboole_0(k7_relat_1('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_4, c_176])).
% 1.83/1.18  tff(c_179, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_178])).
% 1.83/1.18  tff(c_182, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6, c_179])).
% 1.83/1.18  tff(c_186, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_182])).
% 1.83/1.18  tff(c_187, plain, (v1_xboole_0(k7_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_178])).
% 1.83/1.18  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.83/1.18  tff(c_43, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_41, c_2])).
% 1.83/1.18  tff(c_191, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_187, c_43])).
% 1.83/1.18  tff(c_195, plain, $false, inference(negUnitSimplification, [status(thm)], [c_172, c_191])).
% 1.83/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.18  
% 1.83/1.18  Inference rules
% 1.83/1.18  ----------------------
% 1.83/1.18  #Ref     : 0
% 1.83/1.18  #Sup     : 38
% 1.83/1.18  #Fact    : 0
% 1.83/1.18  #Define  : 0
% 1.83/1.18  #Split   : 4
% 1.83/1.18  #Chain   : 0
% 1.83/1.18  #Close   : 0
% 1.83/1.18  
% 1.83/1.18  Ordering : KBO
% 1.83/1.18  
% 1.83/1.18  Simplification rules
% 1.83/1.18  ----------------------
% 1.83/1.18  #Subsume      : 2
% 1.83/1.18  #Demod        : 24
% 1.83/1.18  #Tautology    : 26
% 1.83/1.18  #SimpNegUnit  : 4
% 1.83/1.18  #BackRed      : 3
% 1.83/1.18  
% 1.83/1.18  #Partial instantiations: 0
% 1.83/1.18  #Strategies tried      : 1
% 1.83/1.18  
% 1.83/1.18  Timing (in seconds)
% 1.83/1.18  ----------------------
% 1.83/1.19  Preprocessing        : 0.26
% 1.83/1.19  Parsing              : 0.15
% 1.83/1.19  CNF conversion       : 0.02
% 1.83/1.19  Main loop            : 0.15
% 1.83/1.19  Inferencing          : 0.06
% 1.83/1.19  Reduction            : 0.04
% 1.83/1.19  Demodulation         : 0.03
% 1.83/1.19  BG Simplification    : 0.01
% 1.83/1.19  Subsumption          : 0.02
% 1.83/1.19  Abstraction          : 0.01
% 1.83/1.19  MUC search           : 0.00
% 1.83/1.19  Cooper               : 0.00
% 1.83/1.19  Total                : 0.45
% 1.83/1.19  Index Insertion      : 0.00
% 1.83/1.19  Index Deletion       : 0.00
% 1.83/1.19  Index Matching       : 0.00
% 1.83/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
