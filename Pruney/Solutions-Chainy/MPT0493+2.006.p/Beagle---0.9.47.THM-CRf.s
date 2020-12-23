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
% DateTime   : Thu Dec  3 09:59:36 EST 2020

% Result     : Theorem 4.54s
% Output     : CNFRefutation 4.54s
% Verified   : 
% Statistics : Number of formulae       :   56 (  63 expanded)
%              Number of leaves         :   28 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :   65 (  84 expanded)
%              Number of equality atoms :   25 (  31 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_53,axiom,(
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

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_67,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_71,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_42,plain,(
    k1_relat_1(k7_relat_1('#skF_5','#skF_4')) != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_46,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_24,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),A_7)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_190,plain,(
    ! [A_49,B_50] :
      ( r2_hidden('#skF_3'(A_49,B_50),B_50)
      | r1_xboole_0(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2217,plain,(
    ! [A_172,A_173,B_174] :
      ( ~ r2_hidden('#skF_3'(A_172,k4_xboole_0(A_173,B_174)),B_174)
      | r1_xboole_0(A_172,k4_xboole_0(A_173,B_174)) ) ),
    inference(resolution,[status(thm)],[c_190,c_4])).

tff(c_2263,plain,(
    ! [A_175,A_176] : r1_xboole_0(A_175,k4_xboole_0(A_176,A_175)) ),
    inference(resolution,[status(thm)],[c_24,c_2217])).

tff(c_30,plain,(
    ! [A_17,B_18] :
      ( k4_xboole_0(A_17,B_18) = A_17
      | ~ r1_xboole_0(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2302,plain,(
    ! [A_177,A_178] : k4_xboole_0(A_177,k4_xboole_0(A_178,A_177)) = A_177 ),
    inference(resolution,[status(thm)],[c_2263,c_30])).

tff(c_44,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_32,plain,(
    ! [A_17,B_18] :
      ( r1_xboole_0(A_17,B_18)
      | k4_xboole_0(A_17,B_18) != A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_250,plain,(
    ! [A_62,C_63,B_64] :
      ( r1_xboole_0(A_62,C_63)
      | ~ r1_xboole_0(B_64,C_63)
      | ~ r1_tarski(A_62,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_347,plain,(
    ! [A_75,B_76,A_77] :
      ( r1_xboole_0(A_75,B_76)
      | ~ r1_tarski(A_75,A_77)
      | k4_xboole_0(A_77,B_76) != A_77 ) ),
    inference(resolution,[status(thm)],[c_32,c_250])).

tff(c_350,plain,(
    ! [B_76] :
      ( r1_xboole_0('#skF_4',B_76)
      | k4_xboole_0(k1_relat_1('#skF_5'),B_76) != k1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_44,c_347])).

tff(c_2587,plain,(
    ! [A_180] : r1_xboole_0('#skF_4',k4_xboole_0(A_180,k1_relat_1('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2302,c_350])).

tff(c_3081,plain,(
    ! [A_200] : k4_xboole_0('#skF_4',k4_xboole_0(A_200,k1_relat_1('#skF_5'))) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2587,c_30])).

tff(c_26,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3184,plain,(
    k3_xboole_0('#skF_4',k1_relat_1('#skF_5')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_3081,c_26])).

tff(c_254,plain,(
    ! [B_65,A_66] :
      ( k3_xboole_0(k1_relat_1(B_65),A_66) = k1_relat_1(k7_relat_1(B_65,A_66))
      | ~ v1_relat_1(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_34,plain,(
    ! [B_20,A_19] : k2_tarski(B_20,A_19) = k2_tarski(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_95,plain,(
    ! [A_35,B_36] : k1_setfam_1(k2_tarski(A_35,B_36)) = k3_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_110,plain,(
    ! [B_37,A_38] : k1_setfam_1(k2_tarski(B_37,A_38)) = k3_xboole_0(A_38,B_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_95])).

tff(c_38,plain,(
    ! [A_23,B_24] : k1_setfam_1(k2_tarski(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_116,plain,(
    ! [B_37,A_38] : k3_xboole_0(B_37,A_38) = k3_xboole_0(A_38,B_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_38])).

tff(c_269,plain,(
    ! [A_66,B_65] :
      ( k3_xboole_0(A_66,k1_relat_1(B_65)) = k1_relat_1(k7_relat_1(B_65,A_66))
      | ~ v1_relat_1(B_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_116])).

tff(c_3286,plain,
    ( k1_relat_1(k7_relat_1('#skF_5','#skF_4')) = '#skF_4'
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3184,c_269])).

tff(c_3314,plain,(
    k1_relat_1(k7_relat_1('#skF_5','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_3286])).

tff(c_3316,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_3314])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:07:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.54/1.83  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.54/1.84  
% 4.54/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.54/1.84  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 4.54/1.84  
% 4.54/1.84  %Foreground sorts:
% 4.54/1.84  
% 4.54/1.84  
% 4.54/1.84  %Background operators:
% 4.54/1.84  
% 4.54/1.84  
% 4.54/1.84  %Foreground operators:
% 4.54/1.84  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.54/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.54/1.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.54/1.84  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.54/1.84  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.54/1.84  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.54/1.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.54/1.84  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.54/1.84  tff('#skF_5', type, '#skF_5': $i).
% 4.54/1.84  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.54/1.84  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.54/1.84  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.54/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.54/1.84  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.54/1.84  tff('#skF_4', type, '#skF_4': $i).
% 4.54/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.54/1.84  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.54/1.84  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.54/1.84  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.54/1.84  
% 4.54/1.85  tff(f_82, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 4.54/1.85  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.54/1.85  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 4.54/1.85  tff(f_65, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.54/1.85  tff(f_61, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 4.54/1.85  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.54/1.85  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 4.54/1.85  tff(f_67, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.54/1.85  tff(f_71, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 4.54/1.85  tff(c_42, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_4'))!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.54/1.85  tff(c_46, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.54/1.85  tff(c_24, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), A_7) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.54/1.85  tff(c_190, plain, (![A_49, B_50]: (r2_hidden('#skF_3'(A_49, B_50), B_50) | r1_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.54/1.85  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.54/1.85  tff(c_2217, plain, (![A_172, A_173, B_174]: (~r2_hidden('#skF_3'(A_172, k4_xboole_0(A_173, B_174)), B_174) | r1_xboole_0(A_172, k4_xboole_0(A_173, B_174)))), inference(resolution, [status(thm)], [c_190, c_4])).
% 4.54/1.85  tff(c_2263, plain, (![A_175, A_176]: (r1_xboole_0(A_175, k4_xboole_0(A_176, A_175)))), inference(resolution, [status(thm)], [c_24, c_2217])).
% 4.54/1.85  tff(c_30, plain, (![A_17, B_18]: (k4_xboole_0(A_17, B_18)=A_17 | ~r1_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.54/1.85  tff(c_2302, plain, (![A_177, A_178]: (k4_xboole_0(A_177, k4_xboole_0(A_178, A_177))=A_177)), inference(resolution, [status(thm)], [c_2263, c_30])).
% 4.54/1.85  tff(c_44, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.54/1.85  tff(c_32, plain, (![A_17, B_18]: (r1_xboole_0(A_17, B_18) | k4_xboole_0(A_17, B_18)!=A_17)), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.54/1.85  tff(c_250, plain, (![A_62, C_63, B_64]: (r1_xboole_0(A_62, C_63) | ~r1_xboole_0(B_64, C_63) | ~r1_tarski(A_62, B_64))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.54/1.85  tff(c_347, plain, (![A_75, B_76, A_77]: (r1_xboole_0(A_75, B_76) | ~r1_tarski(A_75, A_77) | k4_xboole_0(A_77, B_76)!=A_77)), inference(resolution, [status(thm)], [c_32, c_250])).
% 4.54/1.85  tff(c_350, plain, (![B_76]: (r1_xboole_0('#skF_4', B_76) | k4_xboole_0(k1_relat_1('#skF_5'), B_76)!=k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_44, c_347])).
% 4.54/1.85  tff(c_2587, plain, (![A_180]: (r1_xboole_0('#skF_4', k4_xboole_0(A_180, k1_relat_1('#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_2302, c_350])).
% 4.54/1.85  tff(c_3081, plain, (![A_200]: (k4_xboole_0('#skF_4', k4_xboole_0(A_200, k1_relat_1('#skF_5')))='#skF_4')), inference(resolution, [status(thm)], [c_2587, c_30])).
% 4.54/1.85  tff(c_26, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.54/1.85  tff(c_3184, plain, (k3_xboole_0('#skF_4', k1_relat_1('#skF_5'))='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_3081, c_26])).
% 4.54/1.85  tff(c_254, plain, (![B_65, A_66]: (k3_xboole_0(k1_relat_1(B_65), A_66)=k1_relat_1(k7_relat_1(B_65, A_66)) | ~v1_relat_1(B_65))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.54/1.85  tff(c_34, plain, (![B_20, A_19]: (k2_tarski(B_20, A_19)=k2_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.54/1.85  tff(c_95, plain, (![A_35, B_36]: (k1_setfam_1(k2_tarski(A_35, B_36))=k3_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.54/1.85  tff(c_110, plain, (![B_37, A_38]: (k1_setfam_1(k2_tarski(B_37, A_38))=k3_xboole_0(A_38, B_37))), inference(superposition, [status(thm), theory('equality')], [c_34, c_95])).
% 4.54/1.85  tff(c_38, plain, (![A_23, B_24]: (k1_setfam_1(k2_tarski(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.54/1.85  tff(c_116, plain, (![B_37, A_38]: (k3_xboole_0(B_37, A_38)=k3_xboole_0(A_38, B_37))), inference(superposition, [status(thm), theory('equality')], [c_110, c_38])).
% 4.54/1.85  tff(c_269, plain, (![A_66, B_65]: (k3_xboole_0(A_66, k1_relat_1(B_65))=k1_relat_1(k7_relat_1(B_65, A_66)) | ~v1_relat_1(B_65))), inference(superposition, [status(thm), theory('equality')], [c_254, c_116])).
% 4.54/1.85  tff(c_3286, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_4'))='#skF_4' | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3184, c_269])).
% 4.54/1.85  tff(c_3314, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_3286])).
% 4.54/1.85  tff(c_3316, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_3314])).
% 4.54/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.54/1.85  
% 4.54/1.85  Inference rules
% 4.54/1.85  ----------------------
% 4.54/1.85  #Ref     : 0
% 4.54/1.85  #Sup     : 857
% 4.54/1.85  #Fact    : 0
% 4.54/1.85  #Define  : 0
% 4.54/1.85  #Split   : 0
% 4.54/1.85  #Chain   : 0
% 4.54/1.85  #Close   : 0
% 4.54/1.85  
% 4.54/1.85  Ordering : KBO
% 4.54/1.85  
% 4.54/1.85  Simplification rules
% 4.54/1.85  ----------------------
% 4.54/1.85  #Subsume      : 61
% 4.54/1.85  #Demod        : 331
% 4.54/1.85  #Tautology    : 171
% 4.54/1.85  #SimpNegUnit  : 1
% 4.54/1.85  #BackRed      : 0
% 4.54/1.85  
% 4.54/1.85  #Partial instantiations: 0
% 4.54/1.85  #Strategies tried      : 1
% 4.54/1.85  
% 4.54/1.85  Timing (in seconds)
% 4.54/1.85  ----------------------
% 4.54/1.86  Preprocessing        : 0.31
% 4.54/1.86  Parsing              : 0.16
% 4.54/1.86  CNF conversion       : 0.02
% 4.54/1.86  Main loop            : 0.74
% 4.54/1.86  Inferencing          : 0.23
% 4.54/1.86  Reduction            : 0.28
% 4.54/1.86  Demodulation         : 0.23
% 4.54/1.86  BG Simplification    : 0.03
% 4.54/1.86  Subsumption          : 0.14
% 4.54/1.86  Abstraction          : 0.04
% 4.54/1.86  MUC search           : 0.00
% 4.54/1.86  Cooper               : 0.00
% 4.54/1.86  Total                : 1.08
% 4.54/1.86  Index Insertion      : 0.00
% 4.54/1.86  Index Deletion       : 0.00
% 4.54/1.86  Index Matching       : 0.00
% 4.54/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
