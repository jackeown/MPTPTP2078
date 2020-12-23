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
% DateTime   : Thu Dec  3 09:56:08 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 178 expanded)
%              Number of leaves         :   25 (  69 expanded)
%              Depth                    :   11
%              Number of atoms          :   82 ( 302 expanded)
%              Number of equality atoms :   24 ( 109 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_53,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_47,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(c_34,plain,(
    ! [A_17] : k1_subset_1(A_17) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_40,plain,
    ( k1_subset_1('#skF_3') != '#skF_4'
    | ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_47,plain,
    ( k1_xboole_0 != '#skF_4'
    | ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_40])).

tff(c_70,plain,(
    ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_47])).

tff(c_46,plain,
    ( r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4'))
    | k1_subset_1('#skF_3') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_48,plain,
    ( r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4'))
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_46])).

tff(c_77,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_48])).

tff(c_28,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_80,plain,(
    ! [A_13] : r1_tarski('#skF_4',A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_28])).

tff(c_88,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_70])).

tff(c_89,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_47])).

tff(c_32,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_66,plain,(
    ! [A_23,B_24] : r1_tarski(k4_xboole_0(A_23,B_24),A_23) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_69,plain,(
    ! [A_16] : r1_tarski(A_16,A_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_66])).

tff(c_146,plain,(
    ! [A_35,B_36] :
      ( k4_xboole_0(A_35,B_36) = k1_xboole_0
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_164,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_69,c_146])).

tff(c_611,plain,(
    ! [A_79,B_80,C_81] :
      ( r2_hidden('#skF_1'(A_79,B_80,C_81),A_79)
      | r2_hidden('#skF_2'(A_79,B_80,C_81),C_81)
      | k4_xboole_0(A_79,B_80) = C_81 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_622,plain,(
    ! [A_79,C_81] :
      ( r2_hidden('#skF_2'(A_79,A_79,C_81),C_81)
      | k4_xboole_0(A_79,A_79) = C_81 ) ),
    inference(resolution,[status(thm)],[c_611,c_16])).

tff(c_685,plain,(
    ! [A_82,C_83] :
      ( r2_hidden('#skF_2'(A_82,A_82,C_83),C_83)
      | k1_xboole_0 = C_83 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_622])).

tff(c_90,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_47])).

tff(c_163,plain,(
    k4_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_90,c_146])).

tff(c_513,plain,(
    ! [D_62,A_63,B_64] :
      ( r2_hidden(D_62,k4_xboole_0(A_63,B_64))
      | r2_hidden(D_62,B_64)
      | ~ r2_hidden(D_62,A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_561,plain,(
    ! [D_70] :
      ( r2_hidden(D_70,k1_xboole_0)
      | r2_hidden(D_70,k3_subset_1('#skF_3','#skF_4'))
      | ~ r2_hidden(D_70,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_513])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_343,plain,(
    ! [A_55,B_56] :
      ( k4_xboole_0(A_55,B_56) = k3_subset_1(A_55,B_56)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_347,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_343])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_351,plain,(
    ! [D_6] :
      ( ~ r2_hidden(D_6,'#skF_4')
      | ~ r2_hidden(D_6,k3_subset_1('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_347,c_4])).

tff(c_574,plain,(
    ! [D_71] :
      ( r2_hidden(D_71,k1_xboole_0)
      | ~ r2_hidden(D_71,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_561,c_351])).

tff(c_308,plain,(
    ! [D_44,A_45,B_46] :
      ( r2_hidden(D_44,A_45)
      | ~ r2_hidden(D_44,k4_xboole_0(A_45,B_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_317,plain,(
    ! [D_44,A_16] :
      ( r2_hidden(D_44,A_16)
      | ~ r2_hidden(D_44,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_308])).

tff(c_585,plain,(
    ! [D_71,A_16] :
      ( r2_hidden(D_71,A_16)
      | ~ r2_hidden(D_71,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_574,c_317])).

tff(c_688,plain,(
    ! [A_82,A_16] :
      ( r2_hidden('#skF_2'(A_82,A_82,'#skF_4'),A_16)
      | k1_xboole_0 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_685,c_585])).

tff(c_715,plain,(
    ! [A_82,A_16] : r2_hidden('#skF_2'(A_82,A_82,'#skF_4'),A_16) ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_688])).

tff(c_729,plain,(
    ! [A_84,A_85] : r2_hidden('#skF_2'(A_84,A_84,'#skF_4'),A_85) ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_688])).

tff(c_326,plain,(
    ! [D_50,B_51,A_52] :
      ( ~ r2_hidden(D_50,B_51)
      | ~ r2_hidden(D_50,k4_xboole_0(A_52,B_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_341,plain,(
    ! [D_50,A_16] :
      ( ~ r2_hidden(D_50,k1_xboole_0)
      | ~ r2_hidden(D_50,A_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_326])).

tff(c_584,plain,(
    ! [D_71,A_16] :
      ( ~ r2_hidden(D_71,A_16)
      | ~ r2_hidden(D_71,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_574,c_341])).

tff(c_734,plain,(
    ! [A_84] : ~ r2_hidden('#skF_2'(A_84,A_84,'#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_729,c_584])).

tff(c_762,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_715,c_734])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:16:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.33  
% 2.09/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.33  %$ r2_hidden > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.09/1.33  
% 2.09/1.33  %Foreground sorts:
% 2.09/1.33  
% 2.09/1.33  
% 2.09/1.33  %Background operators:
% 2.09/1.33  
% 2.09/1.33  
% 2.09/1.33  %Foreground operators:
% 2.09/1.33  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.09/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.09/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.09/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.09/1.33  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.09/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.09/1.33  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.09/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.09/1.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.09/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.09/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.09/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.33  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.09/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.09/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.09/1.33  
% 2.57/1.34  tff(f_53, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.57/1.34  tff(f_64, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 2.57/1.34  tff(f_47, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.57/1.34  tff(f_51, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.57/1.34  tff(f_49, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.57/1.34  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.57/1.34  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.57/1.34  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.57/1.34  tff(c_34, plain, (![A_17]: (k1_subset_1(A_17)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.57/1.34  tff(c_40, plain, (k1_subset_1('#skF_3')!='#skF_4' | ~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.57/1.34  tff(c_47, plain, (k1_xboole_0!='#skF_4' | ~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_40])).
% 2.57/1.34  tff(c_70, plain, (~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_47])).
% 2.57/1.34  tff(c_46, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4')) | k1_subset_1('#skF_3')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.57/1.34  tff(c_48, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4')) | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_46])).
% 2.57/1.34  tff(c_77, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_70, c_48])).
% 2.57/1.34  tff(c_28, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.57/1.34  tff(c_80, plain, (![A_13]: (r1_tarski('#skF_4', A_13))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_28])).
% 2.57/1.34  tff(c_88, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_70])).
% 2.57/1.34  tff(c_89, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_47])).
% 2.57/1.34  tff(c_32, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.57/1.34  tff(c_66, plain, (![A_23, B_24]: (r1_tarski(k4_xboole_0(A_23, B_24), A_23))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.57/1.34  tff(c_69, plain, (![A_16]: (r1_tarski(A_16, A_16))), inference(superposition, [status(thm), theory('equality')], [c_32, c_66])).
% 2.57/1.34  tff(c_146, plain, (![A_35, B_36]: (k4_xboole_0(A_35, B_36)=k1_xboole_0 | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.57/1.34  tff(c_164, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k1_xboole_0)), inference(resolution, [status(thm)], [c_69, c_146])).
% 2.57/1.34  tff(c_611, plain, (![A_79, B_80, C_81]: (r2_hidden('#skF_1'(A_79, B_80, C_81), A_79) | r2_hidden('#skF_2'(A_79, B_80, C_81), C_81) | k4_xboole_0(A_79, B_80)=C_81)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.57/1.34  tff(c_16, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.57/1.34  tff(c_622, plain, (![A_79, C_81]: (r2_hidden('#skF_2'(A_79, A_79, C_81), C_81) | k4_xboole_0(A_79, A_79)=C_81)), inference(resolution, [status(thm)], [c_611, c_16])).
% 2.57/1.34  tff(c_685, plain, (![A_82, C_83]: (r2_hidden('#skF_2'(A_82, A_82, C_83), C_83) | k1_xboole_0=C_83)), inference(demodulation, [status(thm), theory('equality')], [c_164, c_622])).
% 2.57/1.34  tff(c_90, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_47])).
% 2.57/1.34  tff(c_163, plain, (k4_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_90, c_146])).
% 2.57/1.34  tff(c_513, plain, (![D_62, A_63, B_64]: (r2_hidden(D_62, k4_xboole_0(A_63, B_64)) | r2_hidden(D_62, B_64) | ~r2_hidden(D_62, A_63))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.57/1.34  tff(c_561, plain, (![D_70]: (r2_hidden(D_70, k1_xboole_0) | r2_hidden(D_70, k3_subset_1('#skF_3', '#skF_4')) | ~r2_hidden(D_70, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_163, c_513])).
% 2.57/1.34  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.57/1.34  tff(c_343, plain, (![A_55, B_56]: (k4_xboole_0(A_55, B_56)=k3_subset_1(A_55, B_56) | ~m1_subset_1(B_56, k1_zfmisc_1(A_55)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.57/1.34  tff(c_347, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_38, c_343])).
% 2.57/1.34  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.57/1.34  tff(c_351, plain, (![D_6]: (~r2_hidden(D_6, '#skF_4') | ~r2_hidden(D_6, k3_subset_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_347, c_4])).
% 2.57/1.34  tff(c_574, plain, (![D_71]: (r2_hidden(D_71, k1_xboole_0) | ~r2_hidden(D_71, '#skF_4'))), inference(resolution, [status(thm)], [c_561, c_351])).
% 2.57/1.34  tff(c_308, plain, (![D_44, A_45, B_46]: (r2_hidden(D_44, A_45) | ~r2_hidden(D_44, k4_xboole_0(A_45, B_46)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.57/1.34  tff(c_317, plain, (![D_44, A_16]: (r2_hidden(D_44, A_16) | ~r2_hidden(D_44, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_164, c_308])).
% 2.57/1.34  tff(c_585, plain, (![D_71, A_16]: (r2_hidden(D_71, A_16) | ~r2_hidden(D_71, '#skF_4'))), inference(resolution, [status(thm)], [c_574, c_317])).
% 2.57/1.34  tff(c_688, plain, (![A_82, A_16]: (r2_hidden('#skF_2'(A_82, A_82, '#skF_4'), A_16) | k1_xboole_0='#skF_4')), inference(resolution, [status(thm)], [c_685, c_585])).
% 2.57/1.34  tff(c_715, plain, (![A_82, A_16]: (r2_hidden('#skF_2'(A_82, A_82, '#skF_4'), A_16))), inference(negUnitSimplification, [status(thm)], [c_89, c_688])).
% 2.57/1.34  tff(c_729, plain, (![A_84, A_85]: (r2_hidden('#skF_2'(A_84, A_84, '#skF_4'), A_85))), inference(negUnitSimplification, [status(thm)], [c_89, c_688])).
% 2.57/1.34  tff(c_326, plain, (![D_50, B_51, A_52]: (~r2_hidden(D_50, B_51) | ~r2_hidden(D_50, k4_xboole_0(A_52, B_51)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.57/1.34  tff(c_341, plain, (![D_50, A_16]: (~r2_hidden(D_50, k1_xboole_0) | ~r2_hidden(D_50, A_16))), inference(superposition, [status(thm), theory('equality')], [c_32, c_326])).
% 2.57/1.34  tff(c_584, plain, (![D_71, A_16]: (~r2_hidden(D_71, A_16) | ~r2_hidden(D_71, '#skF_4'))), inference(resolution, [status(thm)], [c_574, c_341])).
% 2.57/1.34  tff(c_734, plain, (![A_84]: (~r2_hidden('#skF_2'(A_84, A_84, '#skF_4'), '#skF_4'))), inference(resolution, [status(thm)], [c_729, c_584])).
% 2.57/1.34  tff(c_762, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_715, c_734])).
% 2.57/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.34  
% 2.57/1.34  Inference rules
% 2.57/1.34  ----------------------
% 2.57/1.34  #Ref     : 0
% 2.57/1.34  #Sup     : 170
% 2.57/1.34  #Fact    : 0
% 2.57/1.34  #Define  : 0
% 2.57/1.34  #Split   : 2
% 2.57/1.34  #Chain   : 0
% 2.57/1.34  #Close   : 0
% 2.57/1.34  
% 2.57/1.34  Ordering : KBO
% 2.57/1.34  
% 2.57/1.34  Simplification rules
% 2.57/1.34  ----------------------
% 2.57/1.34  #Subsume      : 16
% 2.57/1.34  #Demod        : 66
% 2.57/1.34  #Tautology    : 100
% 2.57/1.34  #SimpNegUnit  : 5
% 2.57/1.34  #BackRed      : 5
% 2.57/1.34  
% 2.57/1.34  #Partial instantiations: 0
% 2.57/1.34  #Strategies tried      : 1
% 2.57/1.34  
% 2.57/1.34  Timing (in seconds)
% 2.57/1.34  ----------------------
% 2.57/1.34  Preprocessing        : 0.29
% 2.57/1.34  Parsing              : 0.15
% 2.57/1.34  CNF conversion       : 0.02
% 2.57/1.34  Main loop            : 0.29
% 2.57/1.34  Inferencing          : 0.11
% 2.57/1.34  Reduction            : 0.09
% 2.57/1.34  Demodulation         : 0.07
% 2.57/1.34  BG Simplification    : 0.02
% 2.57/1.35  Subsumption          : 0.05
% 2.57/1.35  Abstraction          : 0.02
% 2.57/1.35  MUC search           : 0.00
% 2.57/1.35  Cooper               : 0.00
% 2.57/1.35  Total                : 0.61
% 2.57/1.35  Index Insertion      : 0.00
% 2.57/1.35  Index Deletion       : 0.00
% 2.57/1.35  Index Matching       : 0.00
% 2.57/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
