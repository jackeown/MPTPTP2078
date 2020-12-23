%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:26 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 196 expanded)
%              Number of leaves         :   17 (  73 expanded)
%              Depth                    :   14
%              Number of atoms          :   79 ( 481 expanded)
%              Number of equality atoms :   20 ( 100 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_63,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & v1_zfmisc_1(A) )
       => ! [B] :
            ( ~ v1_xboole_0(k3_xboole_0(A,B))
           => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_51,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(c_26,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_357,plain,(
    ! [A_54,B_55,C_56] :
      ( r2_hidden('#skF_1'(A_54,B_55,C_56),B_55)
      | r2_hidden('#skF_2'(A_54,B_55,C_56),C_56)
      | k3_xboole_0(A_54,B_55) = C_56 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_400,plain,(
    ! [A_54,B_55] :
      ( r2_hidden('#skF_2'(A_54,B_55,B_55),B_55)
      | k3_xboole_0(A_54,B_55) = B_55 ) ),
    inference(resolution,[status(thm)],[c_357,c_14])).

tff(c_410,plain,(
    ! [A_57,B_58] :
      ( r2_hidden('#skF_2'(A_57,B_58,B_58),B_58)
      | k3_xboole_0(A_57,B_58) = B_58 ) ),
    inference(resolution,[status(thm)],[c_357,c_14])).

tff(c_32,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_30,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_20,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_63,plain,(
    ! [B_27,A_28] :
      ( B_27 = A_28
      | ~ r1_tarski(A_28,B_27)
      | ~ v1_zfmisc_1(B_27)
      | v1_xboole_0(B_27)
      | v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_78,plain,(
    ! [A_32,B_33] :
      ( k3_xboole_0(A_32,B_33) = A_32
      | ~ v1_zfmisc_1(A_32)
      | v1_xboole_0(A_32)
      | v1_xboole_0(k3_xboole_0(A_32,B_33)) ) ),
    inference(resolution,[status(thm)],[c_20,c_63])).

tff(c_28,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_81,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = '#skF_3'
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_28])).

tff(c_84,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = '#skF_3'
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_81])).

tff(c_85,plain,(
    k3_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_84])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_102,plain,(
    ! [D_6] :
      ( r2_hidden(D_6,'#skF_4')
      | ~ r2_hidden(D_6,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_4])).

tff(c_433,plain,(
    ! [A_57] :
      ( r2_hidden('#skF_2'(A_57,'#skF_3','#skF_3'),'#skF_4')
      | k3_xboole_0(A_57,'#skF_3') = '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_410,c_102])).

tff(c_798,plain,(
    ! [A_81,B_82,C_83] :
      ( r2_hidden('#skF_1'(A_81,B_82,C_83),B_82)
      | ~ r2_hidden('#skF_2'(A_81,B_82,C_83),B_82)
      | ~ r2_hidden('#skF_2'(A_81,B_82,C_83),A_81)
      | k3_xboole_0(A_81,B_82) = C_83 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_826,plain,
    ( r2_hidden('#skF_1'('#skF_4','#skF_3','#skF_3'),'#skF_3')
    | ~ r2_hidden('#skF_2'('#skF_4','#skF_3','#skF_3'),'#skF_3')
    | k3_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_433,c_798])).

tff(c_882,plain,(
    ~ r2_hidden('#skF_2'('#skF_4','#skF_3','#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_826])).

tff(c_889,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_400,c_882])).

tff(c_911,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_889,c_20])).

tff(c_918,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_911])).

tff(c_920,plain,(
    r2_hidden('#skF_2'('#skF_4','#skF_3','#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_826])).

tff(c_1015,plain,(
    r2_hidden('#skF_2'('#skF_4','#skF_3','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_920,c_102])).

tff(c_919,plain,
    ( k3_xboole_0('#skF_4','#skF_3') = '#skF_3'
    | r2_hidden('#skF_1'('#skF_4','#skF_3','#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_826])).

tff(c_1021,plain,(
    r2_hidden('#skF_1'('#skF_4','#skF_3','#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_919])).

tff(c_8,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1077,plain,
    ( ~ r2_hidden('#skF_2'('#skF_4','#skF_3','#skF_3'),'#skF_3')
    | ~ r2_hidden('#skF_2'('#skF_4','#skF_3','#skF_3'),'#skF_4')
    | k3_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1021,c_8])).

tff(c_1086,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1015,c_920,c_1077])).

tff(c_1119,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1086,c_20])).

tff(c_1128,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_1119])).

tff(c_1129,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_919])).

tff(c_1156,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1129,c_20])).

tff(c_1164,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_1156])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:09:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.16/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.51  
% 3.16/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.51  %$ r2_hidden > r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 3.16/1.51  
% 3.16/1.51  %Foreground sorts:
% 3.16/1.51  
% 3.16/1.51  
% 3.16/1.51  %Background operators:
% 3.16/1.51  
% 3.16/1.51  
% 3.16/1.51  %Foreground operators:
% 3.16/1.51  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.16/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.16/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.16/1.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.16/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.16/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.16/1.51  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.16/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.16/1.51  tff('#skF_4', type, '#skF_4': $i).
% 3.16/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.16/1.51  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.16/1.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.16/1.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.16/1.51  
% 3.16/1.52  tff(f_63, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (~v1_xboole_0(k3_xboole_0(A, B)) => r1_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tex_2)).
% 3.16/1.52  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 3.16/1.52  tff(f_36, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.16/1.52  tff(f_51, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 3.16/1.52  tff(c_26, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.16/1.52  tff(c_357, plain, (![A_54, B_55, C_56]: (r2_hidden('#skF_1'(A_54, B_55, C_56), B_55) | r2_hidden('#skF_2'(A_54, B_55, C_56), C_56) | k3_xboole_0(A_54, B_55)=C_56)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.16/1.52  tff(c_14, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.16/1.52  tff(c_400, plain, (![A_54, B_55]: (r2_hidden('#skF_2'(A_54, B_55, B_55), B_55) | k3_xboole_0(A_54, B_55)=B_55)), inference(resolution, [status(thm)], [c_357, c_14])).
% 3.16/1.52  tff(c_410, plain, (![A_57, B_58]: (r2_hidden('#skF_2'(A_57, B_58, B_58), B_58) | k3_xboole_0(A_57, B_58)=B_58)), inference(resolution, [status(thm)], [c_357, c_14])).
% 3.16/1.52  tff(c_32, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.16/1.52  tff(c_30, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.16/1.52  tff(c_20, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.16/1.52  tff(c_63, plain, (![B_27, A_28]: (B_27=A_28 | ~r1_tarski(A_28, B_27) | ~v1_zfmisc_1(B_27) | v1_xboole_0(B_27) | v1_xboole_0(A_28))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.16/1.52  tff(c_78, plain, (![A_32, B_33]: (k3_xboole_0(A_32, B_33)=A_32 | ~v1_zfmisc_1(A_32) | v1_xboole_0(A_32) | v1_xboole_0(k3_xboole_0(A_32, B_33)))), inference(resolution, [status(thm)], [c_20, c_63])).
% 3.16/1.52  tff(c_28, plain, (~v1_xboole_0(k3_xboole_0('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.16/1.52  tff(c_81, plain, (k3_xboole_0('#skF_3', '#skF_4')='#skF_3' | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_78, c_28])).
% 3.16/1.52  tff(c_84, plain, (k3_xboole_0('#skF_3', '#skF_4')='#skF_3' | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_81])).
% 3.16/1.52  tff(c_85, plain, (k3_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_32, c_84])).
% 3.16/1.52  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.16/1.52  tff(c_102, plain, (![D_6]: (r2_hidden(D_6, '#skF_4') | ~r2_hidden(D_6, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_85, c_4])).
% 3.16/1.52  tff(c_433, plain, (![A_57]: (r2_hidden('#skF_2'(A_57, '#skF_3', '#skF_3'), '#skF_4') | k3_xboole_0(A_57, '#skF_3')='#skF_3')), inference(resolution, [status(thm)], [c_410, c_102])).
% 3.16/1.52  tff(c_798, plain, (![A_81, B_82, C_83]: (r2_hidden('#skF_1'(A_81, B_82, C_83), B_82) | ~r2_hidden('#skF_2'(A_81, B_82, C_83), B_82) | ~r2_hidden('#skF_2'(A_81, B_82, C_83), A_81) | k3_xboole_0(A_81, B_82)=C_83)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.16/1.52  tff(c_826, plain, (r2_hidden('#skF_1'('#skF_4', '#skF_3', '#skF_3'), '#skF_3') | ~r2_hidden('#skF_2'('#skF_4', '#skF_3', '#skF_3'), '#skF_3') | k3_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_433, c_798])).
% 3.16/1.52  tff(c_882, plain, (~r2_hidden('#skF_2'('#skF_4', '#skF_3', '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_826])).
% 3.16/1.52  tff(c_889, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_400, c_882])).
% 3.16/1.52  tff(c_911, plain, (r1_tarski('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_889, c_20])).
% 3.16/1.52  tff(c_918, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_911])).
% 3.16/1.52  tff(c_920, plain, (r2_hidden('#skF_2'('#skF_4', '#skF_3', '#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_826])).
% 3.16/1.52  tff(c_1015, plain, (r2_hidden('#skF_2'('#skF_4', '#skF_3', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_920, c_102])).
% 3.16/1.52  tff(c_919, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_3' | r2_hidden('#skF_1'('#skF_4', '#skF_3', '#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_826])).
% 3.16/1.52  tff(c_1021, plain, (r2_hidden('#skF_1'('#skF_4', '#skF_3', '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_919])).
% 3.16/1.52  tff(c_8, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.16/1.52  tff(c_1077, plain, (~r2_hidden('#skF_2'('#skF_4', '#skF_3', '#skF_3'), '#skF_3') | ~r2_hidden('#skF_2'('#skF_4', '#skF_3', '#skF_3'), '#skF_4') | k3_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_1021, c_8])).
% 3.16/1.52  tff(c_1086, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1015, c_920, c_1077])).
% 3.16/1.52  tff(c_1119, plain, (r1_tarski('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1086, c_20])).
% 3.16/1.52  tff(c_1128, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_1119])).
% 3.16/1.52  tff(c_1129, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_919])).
% 3.16/1.52  tff(c_1156, plain, (r1_tarski('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1129, c_20])).
% 3.16/1.52  tff(c_1164, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_1156])).
% 3.16/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.52  
% 3.16/1.52  Inference rules
% 3.16/1.52  ----------------------
% 3.16/1.52  #Ref     : 0
% 3.16/1.52  #Sup     : 248
% 3.16/1.52  #Fact    : 0
% 3.16/1.52  #Define  : 0
% 3.16/1.52  #Split   : 4
% 3.16/1.52  #Chain   : 0
% 3.16/1.52  #Close   : 0
% 3.16/1.52  
% 3.16/1.52  Ordering : KBO
% 3.16/1.52  
% 3.16/1.52  Simplification rules
% 3.16/1.52  ----------------------
% 3.16/1.52  #Subsume      : 27
% 3.16/1.52  #Demod        : 101
% 3.16/1.52  #Tautology    : 74
% 3.16/1.52  #SimpNegUnit  : 11
% 3.16/1.52  #BackRed      : 1
% 3.16/1.52  
% 3.16/1.52  #Partial instantiations: 0
% 3.16/1.52  #Strategies tried      : 1
% 3.16/1.52  
% 3.16/1.52  Timing (in seconds)
% 3.16/1.52  ----------------------
% 3.16/1.52  Preprocessing        : 0.28
% 3.16/1.52  Parsing              : 0.15
% 3.16/1.52  CNF conversion       : 0.02
% 3.16/1.52  Main loop            : 0.47
% 3.16/1.52  Inferencing          : 0.18
% 3.16/1.52  Reduction            : 0.13
% 3.16/1.52  Demodulation         : 0.09
% 3.16/1.52  BG Simplification    : 0.02
% 3.16/1.52  Subsumption          : 0.10
% 3.16/1.52  Abstraction          : 0.02
% 3.16/1.53  MUC search           : 0.00
% 3.16/1.53  Cooper               : 0.00
% 3.16/1.53  Total                : 0.78
% 3.16/1.53  Index Insertion      : 0.00
% 3.16/1.53  Index Deletion       : 0.00
% 3.16/1.53  Index Matching       : 0.00
% 3.16/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
