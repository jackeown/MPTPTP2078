%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:07 EST 2020

% Result     : Theorem 2.58s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :   55 (  93 expanded)
%              Number of leaves         :   26 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :   64 ( 136 expanded)
%              Number of equality atoms :   22 (  55 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_56,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_54,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_50,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_32,plain,(
    ! [A_17] : k1_subset_1(A_17) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_38,plain,
    ( k1_subset_1('#skF_5') != '#skF_6'
    | ~ r1_tarski('#skF_6',k3_subset_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_45,plain,
    ( k1_xboole_0 != '#skF_6'
    | ~ r1_tarski('#skF_6',k3_subset_1('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_38])).

tff(c_62,plain,(
    ~ r1_tarski('#skF_6',k3_subset_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_45])).

tff(c_44,plain,
    ( r1_tarski('#skF_6',k3_subset_1('#skF_5','#skF_6'))
    | k1_subset_1('#skF_5') = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_46,plain,
    ( r1_tarski('#skF_6',k3_subset_1('#skF_5','#skF_6'))
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_44])).

tff(c_63,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_46])).

tff(c_30,plain,(
    ! [A_16] : k4_xboole_0(k1_xboole_0,A_16) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_65,plain,(
    ! [A_16] : k4_xboole_0('#skF_6',A_16) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_63,c_30])).

tff(c_87,plain,(
    ! [D_28,B_29,A_30] :
      ( ~ r2_hidden(D_28,B_29)
      | ~ r2_hidden(D_28,k4_xboole_0(A_30,B_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_101,plain,(
    ! [D_31,A_32] :
      ( ~ r2_hidden(D_31,A_32)
      | ~ r2_hidden(D_31,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_87])).

tff(c_145,plain,(
    ! [A_42,B_43] :
      ( ~ r2_hidden('#skF_1'(A_42,B_43),'#skF_6')
      | r1_tarski(A_42,B_43) ) ),
    inference(resolution,[status(thm)],[c_6,c_101])).

tff(c_150,plain,(
    ! [B_2] : r1_tarski('#skF_6',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_145])).

tff(c_160,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_62])).

tff(c_161,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_45])).

tff(c_162,plain,(
    r1_tarski('#skF_6',k3_subset_1('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_45])).

tff(c_26,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_4'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_231,plain,(
    ! [C_66,B_67,A_68] :
      ( r2_hidden(C_66,B_67)
      | ~ r2_hidden(C_66,A_68)
      | ~ r1_tarski(A_68,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_276,plain,(
    ! [A_73,B_74] :
      ( r2_hidden('#skF_4'(A_73),B_74)
      | ~ r1_tarski(A_73,B_74)
      | k1_xboole_0 = A_73 ) ),
    inference(resolution,[status(thm)],[c_26,c_231])).

tff(c_36,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_238,plain,(
    ! [A_69,B_70] :
      ( k4_xboole_0(A_69,B_70) = k3_subset_1(A_69,B_70)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_242,plain,(
    k4_xboole_0('#skF_5','#skF_6') = k3_subset_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_238])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_246,plain,(
    ! [D_11] :
      ( ~ r2_hidden(D_11,'#skF_6')
      | ~ r2_hidden(D_11,k3_subset_1('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_10])).

tff(c_896,plain,(
    ! [A_122] :
      ( ~ r2_hidden('#skF_4'(A_122),'#skF_6')
      | ~ r1_tarski(A_122,k3_subset_1('#skF_5','#skF_6'))
      | k1_xboole_0 = A_122 ) ),
    inference(resolution,[status(thm)],[c_276,c_246])).

tff(c_912,plain,
    ( ~ r1_tarski('#skF_6',k3_subset_1('#skF_5','#skF_6'))
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_26,c_896])).

tff(c_921,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_912])).

tff(c_923,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_161,c_921])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:34:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.58/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.39  
% 2.58/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.40  %$ r2_hidden > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1
% 2.87/1.40  
% 2.87/1.40  %Foreground sorts:
% 2.87/1.40  
% 2.87/1.40  
% 2.87/1.40  %Background operators:
% 2.87/1.40  
% 2.87/1.40  
% 2.87/1.40  %Foreground operators:
% 2.87/1.40  tff('#skF_4', type, '#skF_4': $i > $i).
% 2.87/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.87/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.87/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.87/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.87/1.40  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.87/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.87/1.40  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.87/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.87/1.40  tff('#skF_6', type, '#skF_6': $i).
% 2.87/1.40  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.87/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.87/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.87/1.40  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.87/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.87/1.40  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.87/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.87/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.87/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.87/1.40  
% 2.87/1.41  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.87/1.41  tff(f_56, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.87/1.41  tff(f_67, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 2.87/1.41  tff(f_54, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.87/1.41  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.87/1.41  tff(f_50, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.87/1.41  tff(f_60, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.87/1.41  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.87/1.41  tff(c_32, plain, (![A_17]: (k1_subset_1(A_17)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.87/1.41  tff(c_38, plain, (k1_subset_1('#skF_5')!='#skF_6' | ~r1_tarski('#skF_6', k3_subset_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.87/1.41  tff(c_45, plain, (k1_xboole_0!='#skF_6' | ~r1_tarski('#skF_6', k3_subset_1('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_38])).
% 2.87/1.41  tff(c_62, plain, (~r1_tarski('#skF_6', k3_subset_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_45])).
% 2.87/1.41  tff(c_44, plain, (r1_tarski('#skF_6', k3_subset_1('#skF_5', '#skF_6')) | k1_subset_1('#skF_5')='#skF_6'), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.87/1.41  tff(c_46, plain, (r1_tarski('#skF_6', k3_subset_1('#skF_5', '#skF_6')) | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_44])).
% 2.87/1.41  tff(c_63, plain, (k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_62, c_46])).
% 2.87/1.41  tff(c_30, plain, (![A_16]: (k4_xboole_0(k1_xboole_0, A_16)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.87/1.41  tff(c_65, plain, (![A_16]: (k4_xboole_0('#skF_6', A_16)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_63, c_30])).
% 2.87/1.41  tff(c_87, plain, (![D_28, B_29, A_30]: (~r2_hidden(D_28, B_29) | ~r2_hidden(D_28, k4_xboole_0(A_30, B_29)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.87/1.41  tff(c_101, plain, (![D_31, A_32]: (~r2_hidden(D_31, A_32) | ~r2_hidden(D_31, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_65, c_87])).
% 2.87/1.41  tff(c_145, plain, (![A_42, B_43]: (~r2_hidden('#skF_1'(A_42, B_43), '#skF_6') | r1_tarski(A_42, B_43))), inference(resolution, [status(thm)], [c_6, c_101])).
% 2.87/1.41  tff(c_150, plain, (![B_2]: (r1_tarski('#skF_6', B_2))), inference(resolution, [status(thm)], [c_6, c_145])).
% 2.87/1.41  tff(c_160, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_150, c_62])).
% 2.87/1.41  tff(c_161, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_45])).
% 2.87/1.41  tff(c_162, plain, (r1_tarski('#skF_6', k3_subset_1('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_45])).
% 2.87/1.41  tff(c_26, plain, (![A_12]: (r2_hidden('#skF_4'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.87/1.41  tff(c_231, plain, (![C_66, B_67, A_68]: (r2_hidden(C_66, B_67) | ~r2_hidden(C_66, A_68) | ~r1_tarski(A_68, B_67))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.87/1.41  tff(c_276, plain, (![A_73, B_74]: (r2_hidden('#skF_4'(A_73), B_74) | ~r1_tarski(A_73, B_74) | k1_xboole_0=A_73)), inference(resolution, [status(thm)], [c_26, c_231])).
% 2.87/1.41  tff(c_36, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.87/1.41  tff(c_238, plain, (![A_69, B_70]: (k4_xboole_0(A_69, B_70)=k3_subset_1(A_69, B_70) | ~m1_subset_1(B_70, k1_zfmisc_1(A_69)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.87/1.41  tff(c_242, plain, (k4_xboole_0('#skF_5', '#skF_6')=k3_subset_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_36, c_238])).
% 2.87/1.41  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.87/1.41  tff(c_246, plain, (![D_11]: (~r2_hidden(D_11, '#skF_6') | ~r2_hidden(D_11, k3_subset_1('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_242, c_10])).
% 2.87/1.41  tff(c_896, plain, (![A_122]: (~r2_hidden('#skF_4'(A_122), '#skF_6') | ~r1_tarski(A_122, k3_subset_1('#skF_5', '#skF_6')) | k1_xboole_0=A_122)), inference(resolution, [status(thm)], [c_276, c_246])).
% 2.87/1.41  tff(c_912, plain, (~r1_tarski('#skF_6', k3_subset_1('#skF_5', '#skF_6')) | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_26, c_896])).
% 2.87/1.41  tff(c_921, plain, (k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_162, c_912])).
% 2.87/1.41  tff(c_923, plain, $false, inference(negUnitSimplification, [status(thm)], [c_161, c_921])).
% 2.87/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.41  
% 2.87/1.41  Inference rules
% 2.87/1.41  ----------------------
% 2.87/1.41  #Ref     : 0
% 2.87/1.41  #Sup     : 184
% 2.87/1.41  #Fact    : 0
% 2.87/1.41  #Define  : 0
% 2.87/1.41  #Split   : 4
% 2.87/1.41  #Chain   : 0
% 2.87/1.41  #Close   : 0
% 2.87/1.41  
% 2.87/1.41  Ordering : KBO
% 2.87/1.41  
% 2.87/1.41  Simplification rules
% 2.87/1.41  ----------------------
% 2.87/1.41  #Subsume      : 16
% 2.87/1.41  #Demod        : 47
% 2.87/1.41  #Tautology    : 59
% 2.87/1.41  #SimpNegUnit  : 11
% 2.87/1.41  #BackRed      : 11
% 2.87/1.41  
% 2.87/1.41  #Partial instantiations: 0
% 2.87/1.41  #Strategies tried      : 1
% 2.87/1.41  
% 2.87/1.41  Timing (in seconds)
% 2.87/1.41  ----------------------
% 2.87/1.41  Preprocessing        : 0.30
% 2.87/1.41  Parsing              : 0.15
% 2.87/1.41  CNF conversion       : 0.02
% 2.87/1.41  Main loop            : 0.36
% 2.87/1.41  Inferencing          : 0.13
% 2.87/1.41  Reduction            : 0.10
% 2.87/1.41  Demodulation         : 0.07
% 2.87/1.41  BG Simplification    : 0.02
% 2.87/1.41  Subsumption          : 0.07
% 2.87/1.41  Abstraction          : 0.02
% 2.87/1.41  MUC search           : 0.00
% 2.87/1.41  Cooper               : 0.00
% 2.87/1.41  Total                : 0.68
% 2.87/1.41  Index Insertion      : 0.00
% 2.87/1.41  Index Deletion       : 0.00
% 2.87/1.41  Index Matching       : 0.00
% 2.87/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
