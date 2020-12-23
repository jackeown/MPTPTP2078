%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:49 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 134 expanded)
%              Number of leaves         :   23 (  55 expanded)
%              Depth                    :    9
%              Number of atoms          :   85 ( 269 expanded)
%              Number of equality atoms :   17 (  65 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(B,A)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_60,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_44,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_26,plain,(
    ! [A_12,B_13] :
      ( r2_xboole_0(A_12,B_13)
      | B_13 = A_12
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_34,plain,(
    ! [A_14,B_15] :
      ( r2_hidden('#skF_4'(A_14,B_15),B_15)
      | ~ r2_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_261,plain,(
    ! [A_75,B_76,C_77,D_78] :
      ( r2_hidden(k4_tarski(A_75,B_76),k2_zfmisc_1(C_77,D_78))
      | ~ r2_hidden(B_76,D_78)
      | ~ r2_hidden(A_75,C_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_50,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = k2_zfmisc_1('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_202,plain,(
    ! [A_59,C_60,B_61,D_62] :
      ( r2_hidden(A_59,C_60)
      | ~ r2_hidden(k4_tarski(A_59,B_61),k2_zfmisc_1(C_60,D_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_205,plain,(
    ! [A_59,B_61] :
      ( r2_hidden(A_59,'#skF_5')
      | ~ r2_hidden(k4_tarski(A_59,B_61),k2_zfmisc_1('#skF_6','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_202])).

tff(c_281,plain,(
    ! [A_75,B_76] :
      ( r2_hidden(A_75,'#skF_5')
      | ~ r2_hidden(B_76,'#skF_5')
      | ~ r2_hidden(A_75,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_261,c_205])).

tff(c_298,plain,(
    ! [B_81] : ~ r2_hidden(B_81,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_281])).

tff(c_314,plain,(
    ! [B_82] : r1_tarski('#skF_5',B_82) ),
    inference(resolution,[status(thm)],[c_6,c_298])).

tff(c_36,plain,(
    ! [A_17] : k3_xboole_0(A_17,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_76,plain,(
    ! [D_30,A_31,B_32] :
      ( r2_hidden(D_30,A_31)
      | ~ r2_hidden(D_30,k3_xboole_0(A_31,B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_85,plain,(
    ! [D_33,A_34] :
      ( r2_hidden(D_33,A_34)
      | ~ r2_hidden(D_33,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_76])).

tff(c_149,plain,(
    ! [A_48,A_49] :
      ( r2_hidden('#skF_4'(A_48,k1_xboole_0),A_49)
      | ~ r2_xboole_0(A_48,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_34,c_85])).

tff(c_32,plain,(
    ! [A_14,B_15] :
      ( ~ r2_hidden('#skF_4'(A_14,B_15),A_14)
      | ~ r2_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_179,plain,(
    ! [A_53] : ~ r2_xboole_0(A_53,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_149,c_32])).

tff(c_184,plain,(
    ! [A_12] :
      ( k1_xboole_0 = A_12
      | ~ r1_tarski(A_12,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_26,c_179])).

tff(c_320,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_314,c_184])).

tff(c_325,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_320])).

tff(c_327,plain,(
    ! [A_83] :
      ( r2_hidden(A_83,'#skF_5')
      | ~ r2_hidden(A_83,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_281])).

tff(c_374,plain,(
    ! [B_87] :
      ( ~ r2_xboole_0('#skF_5',B_87)
      | ~ r2_hidden('#skF_4'('#skF_5',B_87),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_327,c_32])).

tff(c_384,plain,(
    ~ r2_xboole_0('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_34,c_374])).

tff(c_387,plain,
    ( '#skF_5' = '#skF_6'
    | ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_26,c_384])).

tff(c_390,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_387])).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_198,plain,(
    ! [B_55,D_56,A_57,C_58] :
      ( r2_hidden(B_55,D_56)
      | ~ r2_hidden(k4_tarski(A_57,B_55),k2_zfmisc_1(C_58,D_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_201,plain,(
    ! [B_55,A_57] :
      ( r2_hidden(B_55,'#skF_6')
      | ~ r2_hidden(k4_tarski(A_57,B_55),k2_zfmisc_1('#skF_6','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_198])).

tff(c_282,plain,(
    ! [B_76,A_75] :
      ( r2_hidden(B_76,'#skF_6')
      | ~ r2_hidden(B_76,'#skF_5')
      | ~ r2_hidden(A_75,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_261,c_201])).

tff(c_473,plain,(
    ! [A_96] : ~ r2_hidden(A_96,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_282])).

tff(c_504,plain,(
    ! [B_97] : r1_tarski('#skF_6',B_97) ),
    inference(resolution,[status(thm)],[c_6,c_473])).

tff(c_513,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_504,c_184])).

tff(c_520,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_513])).

tff(c_573,plain,(
    ! [B_100] :
      ( r2_hidden(B_100,'#skF_6')
      | ~ r2_hidden(B_100,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_282])).

tff(c_607,plain,(
    ! [B_101] :
      ( r2_hidden('#skF_1'('#skF_5',B_101),'#skF_6')
      | r1_tarski('#skF_5',B_101) ) ),
    inference(resolution,[status(thm)],[c_6,c_573])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_617,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_607,c_4])).

tff(c_624,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_390,c_390,c_617])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:37:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.40  
% 2.49/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.40  %$ r2_xboole_0 > r2_hidden > r1_tarski > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.49/1.40  
% 2.49/1.40  %Foreground sorts:
% 2.49/1.40  
% 2.49/1.40  
% 2.49/1.40  %Background operators:
% 2.49/1.40  
% 2.49/1.40  
% 2.49/1.40  %Foreground operators:
% 2.49/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.49/1.40  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.49/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.49/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.49/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.49/1.40  tff('#skF_6', type, '#skF_6': $i).
% 2.49/1.40  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.49/1.40  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.49/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.49/1.40  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.49/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.49/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.49/1.40  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.49/1.40  
% 2.49/1.42  tff(f_75, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(B, A)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t114_zfmisc_1)).
% 2.49/1.42  tff(f_48, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.49/1.42  tff(f_58, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_0)).
% 2.49/1.42  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.49/1.42  tff(f_66, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.49/1.42  tff(f_60, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.49/1.42  tff(f_41, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.49/1.42  tff(c_44, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.49/1.42  tff(c_26, plain, (![A_12, B_13]: (r2_xboole_0(A_12, B_13) | B_13=A_12 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.49/1.42  tff(c_34, plain, (![A_14, B_15]: (r2_hidden('#skF_4'(A_14, B_15), B_15) | ~r2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.49/1.42  tff(c_48, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.49/1.42  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.49/1.42  tff(c_261, plain, (![A_75, B_76, C_77, D_78]: (r2_hidden(k4_tarski(A_75, B_76), k2_zfmisc_1(C_77, D_78)) | ~r2_hidden(B_76, D_78) | ~r2_hidden(A_75, C_77))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.49/1.42  tff(c_50, plain, (k2_zfmisc_1('#skF_5', '#skF_6')=k2_zfmisc_1('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.49/1.42  tff(c_202, plain, (![A_59, C_60, B_61, D_62]: (r2_hidden(A_59, C_60) | ~r2_hidden(k4_tarski(A_59, B_61), k2_zfmisc_1(C_60, D_62)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.49/1.42  tff(c_205, plain, (![A_59, B_61]: (r2_hidden(A_59, '#skF_5') | ~r2_hidden(k4_tarski(A_59, B_61), k2_zfmisc_1('#skF_6', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_50, c_202])).
% 2.49/1.42  tff(c_281, plain, (![A_75, B_76]: (r2_hidden(A_75, '#skF_5') | ~r2_hidden(B_76, '#skF_5') | ~r2_hidden(A_75, '#skF_6'))), inference(resolution, [status(thm)], [c_261, c_205])).
% 2.49/1.42  tff(c_298, plain, (![B_81]: (~r2_hidden(B_81, '#skF_5'))), inference(splitLeft, [status(thm)], [c_281])).
% 2.49/1.42  tff(c_314, plain, (![B_82]: (r1_tarski('#skF_5', B_82))), inference(resolution, [status(thm)], [c_6, c_298])).
% 2.49/1.42  tff(c_36, plain, (![A_17]: (k3_xboole_0(A_17, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.49/1.42  tff(c_76, plain, (![D_30, A_31, B_32]: (r2_hidden(D_30, A_31) | ~r2_hidden(D_30, k3_xboole_0(A_31, B_32)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.49/1.42  tff(c_85, plain, (![D_33, A_34]: (r2_hidden(D_33, A_34) | ~r2_hidden(D_33, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_36, c_76])).
% 2.49/1.42  tff(c_149, plain, (![A_48, A_49]: (r2_hidden('#skF_4'(A_48, k1_xboole_0), A_49) | ~r2_xboole_0(A_48, k1_xboole_0))), inference(resolution, [status(thm)], [c_34, c_85])).
% 2.49/1.42  tff(c_32, plain, (![A_14, B_15]: (~r2_hidden('#skF_4'(A_14, B_15), A_14) | ~r2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.49/1.42  tff(c_179, plain, (![A_53]: (~r2_xboole_0(A_53, k1_xboole_0))), inference(resolution, [status(thm)], [c_149, c_32])).
% 2.49/1.42  tff(c_184, plain, (![A_12]: (k1_xboole_0=A_12 | ~r1_tarski(A_12, k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_179])).
% 2.49/1.42  tff(c_320, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_314, c_184])).
% 2.49/1.42  tff(c_325, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_320])).
% 2.49/1.42  tff(c_327, plain, (![A_83]: (r2_hidden(A_83, '#skF_5') | ~r2_hidden(A_83, '#skF_6'))), inference(splitRight, [status(thm)], [c_281])).
% 2.49/1.42  tff(c_374, plain, (![B_87]: (~r2_xboole_0('#skF_5', B_87) | ~r2_hidden('#skF_4'('#skF_5', B_87), '#skF_6'))), inference(resolution, [status(thm)], [c_327, c_32])).
% 2.49/1.42  tff(c_384, plain, (~r2_xboole_0('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_34, c_374])).
% 2.49/1.42  tff(c_387, plain, ('#skF_5'='#skF_6' | ~r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_26, c_384])).
% 2.49/1.42  tff(c_390, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_44, c_387])).
% 2.49/1.42  tff(c_46, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.49/1.42  tff(c_198, plain, (![B_55, D_56, A_57, C_58]: (r2_hidden(B_55, D_56) | ~r2_hidden(k4_tarski(A_57, B_55), k2_zfmisc_1(C_58, D_56)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.49/1.42  tff(c_201, plain, (![B_55, A_57]: (r2_hidden(B_55, '#skF_6') | ~r2_hidden(k4_tarski(A_57, B_55), k2_zfmisc_1('#skF_6', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_50, c_198])).
% 2.49/1.42  tff(c_282, plain, (![B_76, A_75]: (r2_hidden(B_76, '#skF_6') | ~r2_hidden(B_76, '#skF_5') | ~r2_hidden(A_75, '#skF_6'))), inference(resolution, [status(thm)], [c_261, c_201])).
% 2.49/1.42  tff(c_473, plain, (![A_96]: (~r2_hidden(A_96, '#skF_6'))), inference(splitLeft, [status(thm)], [c_282])).
% 2.49/1.42  tff(c_504, plain, (![B_97]: (r1_tarski('#skF_6', B_97))), inference(resolution, [status(thm)], [c_6, c_473])).
% 2.49/1.42  tff(c_513, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_504, c_184])).
% 2.49/1.42  tff(c_520, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_513])).
% 2.49/1.42  tff(c_573, plain, (![B_100]: (r2_hidden(B_100, '#skF_6') | ~r2_hidden(B_100, '#skF_5'))), inference(splitRight, [status(thm)], [c_282])).
% 2.49/1.42  tff(c_607, plain, (![B_101]: (r2_hidden('#skF_1'('#skF_5', B_101), '#skF_6') | r1_tarski('#skF_5', B_101))), inference(resolution, [status(thm)], [c_6, c_573])).
% 2.49/1.42  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.49/1.42  tff(c_617, plain, (r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_607, c_4])).
% 2.49/1.42  tff(c_624, plain, $false, inference(negUnitSimplification, [status(thm)], [c_390, c_390, c_617])).
% 2.49/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.42  
% 2.49/1.42  Inference rules
% 2.49/1.42  ----------------------
% 2.49/1.42  #Ref     : 0
% 2.49/1.42  #Sup     : 112
% 2.49/1.42  #Fact    : 0
% 2.49/1.42  #Define  : 0
% 2.49/1.42  #Split   : 3
% 2.49/1.42  #Chain   : 0
% 2.49/1.42  #Close   : 0
% 2.49/1.42  
% 2.49/1.42  Ordering : KBO
% 2.49/1.42  
% 2.49/1.42  Simplification rules
% 2.49/1.42  ----------------------
% 2.49/1.42  #Subsume      : 26
% 2.49/1.42  #Demod        : 6
% 2.49/1.42  #Tautology    : 20
% 2.49/1.42  #SimpNegUnit  : 13
% 2.49/1.42  #BackRed      : 3
% 2.49/1.42  
% 2.49/1.42  #Partial instantiations: 0
% 2.49/1.42  #Strategies tried      : 1
% 2.49/1.42  
% 2.49/1.42  Timing (in seconds)
% 2.49/1.42  ----------------------
% 2.49/1.42  Preprocessing        : 0.31
% 2.49/1.42  Parsing              : 0.16
% 2.49/1.42  CNF conversion       : 0.02
% 2.49/1.42  Main loop            : 0.28
% 2.49/1.42  Inferencing          : 0.11
% 2.49/1.42  Reduction            : 0.07
% 2.49/1.42  Demodulation         : 0.04
% 2.49/1.42  BG Simplification    : 0.02
% 2.49/1.42  Subsumption          : 0.07
% 2.49/1.42  Abstraction          : 0.01
% 2.49/1.42  MUC search           : 0.00
% 2.49/1.42  Cooper               : 0.00
% 2.49/1.42  Total                : 0.61
% 2.49/1.42  Index Insertion      : 0.00
% 2.49/1.42  Index Deletion       : 0.00
% 2.49/1.42  Index Matching       : 0.00
% 2.49/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
