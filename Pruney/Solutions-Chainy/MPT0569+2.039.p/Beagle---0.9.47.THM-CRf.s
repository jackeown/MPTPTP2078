%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:41 EST 2020

% Result     : Theorem 25.20s
% Output     : CNFRefutation 25.20s
% Verified   : 
% Statistics : Number of formulae       :   75 (  94 expanded)
%              Number of leaves         :   38 (  50 expanded)
%              Depth                    :   11
%              Number of atoms          :  111 ( 167 expanded)
%              Number of equality atoms :   13 (  25 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_121,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k10_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_95,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_59,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(c_60,plain,
    ( ~ r1_xboole_0(k2_relat_1('#skF_6'),'#skF_5')
    | k10_relat_1('#skF_6','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_125,plain,(
    k10_relat_1('#skF_6','#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_10,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_58,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_48,plain,(
    ! [A_46,B_47,C_48] :
      ( r2_hidden('#skF_4'(A_46,B_47,C_48),B_47)
      | ~ r2_hidden(A_46,k10_relat_1(C_48,B_47))
      | ~ v1_relat_1(C_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_602,plain,(
    ! [A_142,B_143,C_144] :
      ( r2_hidden('#skF_4'(A_142,B_143,C_144),k2_relat_1(C_144))
      | ~ r2_hidden(A_142,k10_relat_1(C_144,B_143))
      | ~ v1_relat_1(C_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_66,plain,
    ( k10_relat_1('#skF_6','#skF_5') = k1_xboole_0
    | r1_xboole_0(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_169,plain,(
    r1_xboole_0(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_66])).

tff(c_229,plain,(
    ! [A_84,B_85,C_86] :
      ( ~ r1_xboole_0(A_84,B_85)
      | ~ r2_hidden(C_86,B_85)
      | ~ r2_hidden(C_86,A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_239,plain,(
    ! [C_86] :
      ( ~ r2_hidden(C_86,'#skF_5')
      | ~ r2_hidden(C_86,k2_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_169,c_229])).

tff(c_606,plain,(
    ! [A_142,B_143] :
      ( ~ r2_hidden('#skF_4'(A_142,B_143,'#skF_6'),'#skF_5')
      | ~ r2_hidden(A_142,k10_relat_1('#skF_6',B_143))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_602,c_239])).

tff(c_662,plain,(
    ! [A_153,B_154] :
      ( ~ r2_hidden('#skF_4'(A_153,B_154,'#skF_6'),'#skF_5')
      | ~ r2_hidden(A_153,k10_relat_1('#skF_6',B_154)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_606])).

tff(c_666,plain,(
    ! [A_46] :
      ( ~ r2_hidden(A_46,k10_relat_1('#skF_6','#skF_5'))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_48,c_662])).

tff(c_670,plain,(
    ! [A_155] : ~ r2_hidden(A_155,k10_relat_1('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_666])).

tff(c_694,plain,(
    k10_relat_1('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_670])).

tff(c_703,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_694])).

tff(c_704,plain,(
    ~ r1_xboole_0(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_44,plain,(
    ! [A_45] :
      ( k9_relat_1(A_45,k1_relat_1(A_45)) = k2_relat_1(A_45)
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_14,plain,(
    ! [A_12] : k4_xboole_0(k1_xboole_0,A_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_83,plain,(
    ! [C_57,B_58] : ~ r2_hidden(C_57,k4_xboole_0(B_58,k1_tarski(C_57))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_86,plain,(
    ! [C_57] : ~ r2_hidden(C_57,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_83])).

tff(c_705,plain,(
    k10_relat_1('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_40,plain,(
    ! [A_39,B_40,C_41] :
      ( r2_hidden(k4_tarski('#skF_3'(A_39,B_40,C_41),A_39),C_41)
      | ~ r2_hidden(A_39,k9_relat_1(C_41,B_40))
      | ~ v1_relat_1(C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1592,plain,(
    ! [A_275,C_276,B_277,D_278] :
      ( r2_hidden(A_275,k10_relat_1(C_276,B_277))
      | ~ r2_hidden(D_278,B_277)
      | ~ r2_hidden(k4_tarski(A_275,D_278),C_276)
      | ~ r2_hidden(D_278,k2_relat_1(C_276))
      | ~ v1_relat_1(C_276) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_5021,plain,(
    ! [A_566,C_567,A_568,B_569] :
      ( r2_hidden(A_566,k10_relat_1(C_567,A_568))
      | ~ r2_hidden(k4_tarski(A_566,'#skF_1'(A_568,B_569)),C_567)
      | ~ r2_hidden('#skF_1'(A_568,B_569),k2_relat_1(C_567))
      | ~ v1_relat_1(C_567)
      | r1_xboole_0(A_568,B_569) ) ),
    inference(resolution,[status(thm)],[c_8,c_1592])).

tff(c_46299,plain,(
    ! [A_2320,B_2321,B_2322,C_2323] :
      ( r2_hidden('#skF_3'('#skF_1'(A_2320,B_2321),B_2322,C_2323),k10_relat_1(C_2323,A_2320))
      | ~ r2_hidden('#skF_1'(A_2320,B_2321),k2_relat_1(C_2323))
      | r1_xboole_0(A_2320,B_2321)
      | ~ r2_hidden('#skF_1'(A_2320,B_2321),k9_relat_1(C_2323,B_2322))
      | ~ v1_relat_1(C_2323) ) ),
    inference(resolution,[status(thm)],[c_40,c_5021])).

tff(c_46523,plain,(
    ! [B_2321,B_2322] :
      ( r2_hidden('#skF_3'('#skF_1'('#skF_5',B_2321),B_2322,'#skF_6'),k1_xboole_0)
      | ~ r2_hidden('#skF_1'('#skF_5',B_2321),k2_relat_1('#skF_6'))
      | r1_xboole_0('#skF_5',B_2321)
      | ~ r2_hidden('#skF_1'('#skF_5',B_2321),k9_relat_1('#skF_6',B_2322))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_705,c_46299])).

tff(c_46592,plain,(
    ! [B_2321,B_2322] :
      ( r2_hidden('#skF_3'('#skF_1'('#skF_5',B_2321),B_2322,'#skF_6'),k1_xboole_0)
      | ~ r2_hidden('#skF_1'('#skF_5',B_2321),k2_relat_1('#skF_6'))
      | r1_xboole_0('#skF_5',B_2321)
      | ~ r2_hidden('#skF_1'('#skF_5',B_2321),k9_relat_1('#skF_6',B_2322)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_46523])).

tff(c_46594,plain,(
    ! [B_2324,B_2325] :
      ( ~ r2_hidden('#skF_1'('#skF_5',B_2324),k2_relat_1('#skF_6'))
      | r1_xboole_0('#skF_5',B_2324)
      | ~ r2_hidden('#skF_1'('#skF_5',B_2324),k9_relat_1('#skF_6',B_2325)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_46592])).

tff(c_46704,plain,(
    ! [B_2324] :
      ( ~ r2_hidden('#skF_1'('#skF_5',B_2324),k2_relat_1('#skF_6'))
      | r1_xboole_0('#skF_5',B_2324)
      | ~ r2_hidden('#skF_1'('#skF_5',B_2324),k2_relat_1('#skF_6'))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_46594])).

tff(c_46758,plain,(
    ! [B_2326] :
      ( r1_xboole_0('#skF_5',B_2326)
      | ~ r2_hidden('#skF_1'('#skF_5',B_2326),k2_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_46704])).

tff(c_46794,plain,(
    r1_xboole_0('#skF_5',k2_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_6,c_46758])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_46798,plain,(
    r1_xboole_0(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_46794,c_2])).

tff(c_46803,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_704,c_46798])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:54:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 25.20/16.95  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 25.20/16.95  
% 25.20/16.95  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 25.20/16.95  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_1
% 25.20/16.95  
% 25.20/16.95  %Foreground sorts:
% 25.20/16.95  
% 25.20/16.95  
% 25.20/16.95  %Background operators:
% 25.20/16.95  
% 25.20/16.95  
% 25.20/16.95  %Foreground operators:
% 25.20/16.95  tff('#skF_2', type, '#skF_2': $i > $i).
% 25.20/16.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 25.20/16.95  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 25.20/16.95  tff(k1_tarski, type, k1_tarski: $i > $i).
% 25.20/16.95  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 25.20/16.95  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 25.20/16.95  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 25.20/16.95  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 25.20/16.95  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 25.20/16.95  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 25.20/16.95  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 25.20/16.95  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 25.20/16.95  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 25.20/16.95  tff('#skF_5', type, '#skF_5': $i).
% 25.20/16.95  tff('#skF_6', type, '#skF_6': $i).
% 25.20/16.95  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 25.20/16.95  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 25.20/16.95  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 25.20/16.95  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 25.20/16.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 25.20/16.95  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 25.20/16.95  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 25.20/16.95  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 25.20/16.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 25.20/16.95  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 25.20/16.95  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 25.20/16.95  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 25.20/16.95  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 25.20/16.95  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 25.20/16.95  
% 25.20/16.97  tff(f_121, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 25.20/16.97  tff(f_55, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 25.20/16.97  tff(f_106, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 25.20/16.97  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 25.20/16.97  tff(f_95, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 25.20/16.97  tff(f_59, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 25.20/16.97  tff(f_78, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 25.20/16.97  tff(f_91, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 25.20/16.97  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 25.20/16.97  tff(c_60, plain, (~r1_xboole_0(k2_relat_1('#skF_6'), '#skF_5') | k10_relat_1('#skF_6', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_121])).
% 25.20/16.97  tff(c_125, plain, (k10_relat_1('#skF_6', '#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_60])).
% 25.20/16.97  tff(c_10, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_55])).
% 25.20/16.97  tff(c_58, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_121])).
% 25.20/16.97  tff(c_48, plain, (![A_46, B_47, C_48]: (r2_hidden('#skF_4'(A_46, B_47, C_48), B_47) | ~r2_hidden(A_46, k10_relat_1(C_48, B_47)) | ~v1_relat_1(C_48))), inference(cnfTransformation, [status(thm)], [f_106])).
% 25.20/16.97  tff(c_602, plain, (![A_142, B_143, C_144]: (r2_hidden('#skF_4'(A_142, B_143, C_144), k2_relat_1(C_144)) | ~r2_hidden(A_142, k10_relat_1(C_144, B_143)) | ~v1_relat_1(C_144))), inference(cnfTransformation, [status(thm)], [f_106])).
% 25.20/16.97  tff(c_66, plain, (k10_relat_1('#skF_6', '#skF_5')=k1_xboole_0 | r1_xboole_0(k2_relat_1('#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_121])).
% 25.20/16.97  tff(c_169, plain, (r1_xboole_0(k2_relat_1('#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_125, c_66])).
% 25.20/16.97  tff(c_229, plain, (![A_84, B_85, C_86]: (~r1_xboole_0(A_84, B_85) | ~r2_hidden(C_86, B_85) | ~r2_hidden(C_86, A_84))), inference(cnfTransformation, [status(thm)], [f_47])).
% 25.20/16.97  tff(c_239, plain, (![C_86]: (~r2_hidden(C_86, '#skF_5') | ~r2_hidden(C_86, k2_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_169, c_229])).
% 25.20/16.97  tff(c_606, plain, (![A_142, B_143]: (~r2_hidden('#skF_4'(A_142, B_143, '#skF_6'), '#skF_5') | ~r2_hidden(A_142, k10_relat_1('#skF_6', B_143)) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_602, c_239])).
% 25.20/16.97  tff(c_662, plain, (![A_153, B_154]: (~r2_hidden('#skF_4'(A_153, B_154, '#skF_6'), '#skF_5') | ~r2_hidden(A_153, k10_relat_1('#skF_6', B_154)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_606])).
% 25.20/16.97  tff(c_666, plain, (![A_46]: (~r2_hidden(A_46, k10_relat_1('#skF_6', '#skF_5')) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_48, c_662])).
% 25.20/16.97  tff(c_670, plain, (![A_155]: (~r2_hidden(A_155, k10_relat_1('#skF_6', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_666])).
% 25.20/16.97  tff(c_694, plain, (k10_relat_1('#skF_6', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_670])).
% 25.20/16.97  tff(c_703, plain, $false, inference(negUnitSimplification, [status(thm)], [c_125, c_694])).
% 25.20/16.97  tff(c_704, plain, (~r1_xboole_0(k2_relat_1('#skF_6'), '#skF_5')), inference(splitRight, [status(thm)], [c_60])).
% 25.20/16.97  tff(c_6, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 25.20/16.97  tff(c_44, plain, (![A_45]: (k9_relat_1(A_45, k1_relat_1(A_45))=k2_relat_1(A_45) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_95])).
% 25.20/16.97  tff(c_14, plain, (![A_12]: (k4_xboole_0(k1_xboole_0, A_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 25.20/16.97  tff(c_83, plain, (![C_57, B_58]: (~r2_hidden(C_57, k4_xboole_0(B_58, k1_tarski(C_57))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 25.20/16.97  tff(c_86, plain, (![C_57]: (~r2_hidden(C_57, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_83])).
% 25.20/16.97  tff(c_705, plain, (k10_relat_1('#skF_6', '#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_60])).
% 25.20/16.97  tff(c_40, plain, (![A_39, B_40, C_41]: (r2_hidden(k4_tarski('#skF_3'(A_39, B_40, C_41), A_39), C_41) | ~r2_hidden(A_39, k9_relat_1(C_41, B_40)) | ~v1_relat_1(C_41))), inference(cnfTransformation, [status(thm)], [f_91])).
% 25.20/16.97  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 25.20/16.97  tff(c_1592, plain, (![A_275, C_276, B_277, D_278]: (r2_hidden(A_275, k10_relat_1(C_276, B_277)) | ~r2_hidden(D_278, B_277) | ~r2_hidden(k4_tarski(A_275, D_278), C_276) | ~r2_hidden(D_278, k2_relat_1(C_276)) | ~v1_relat_1(C_276))), inference(cnfTransformation, [status(thm)], [f_106])).
% 25.20/16.97  tff(c_5021, plain, (![A_566, C_567, A_568, B_569]: (r2_hidden(A_566, k10_relat_1(C_567, A_568)) | ~r2_hidden(k4_tarski(A_566, '#skF_1'(A_568, B_569)), C_567) | ~r2_hidden('#skF_1'(A_568, B_569), k2_relat_1(C_567)) | ~v1_relat_1(C_567) | r1_xboole_0(A_568, B_569))), inference(resolution, [status(thm)], [c_8, c_1592])).
% 25.20/16.97  tff(c_46299, plain, (![A_2320, B_2321, B_2322, C_2323]: (r2_hidden('#skF_3'('#skF_1'(A_2320, B_2321), B_2322, C_2323), k10_relat_1(C_2323, A_2320)) | ~r2_hidden('#skF_1'(A_2320, B_2321), k2_relat_1(C_2323)) | r1_xboole_0(A_2320, B_2321) | ~r2_hidden('#skF_1'(A_2320, B_2321), k9_relat_1(C_2323, B_2322)) | ~v1_relat_1(C_2323))), inference(resolution, [status(thm)], [c_40, c_5021])).
% 25.20/16.97  tff(c_46523, plain, (![B_2321, B_2322]: (r2_hidden('#skF_3'('#skF_1'('#skF_5', B_2321), B_2322, '#skF_6'), k1_xboole_0) | ~r2_hidden('#skF_1'('#skF_5', B_2321), k2_relat_1('#skF_6')) | r1_xboole_0('#skF_5', B_2321) | ~r2_hidden('#skF_1'('#skF_5', B_2321), k9_relat_1('#skF_6', B_2322)) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_705, c_46299])).
% 25.20/16.97  tff(c_46592, plain, (![B_2321, B_2322]: (r2_hidden('#skF_3'('#skF_1'('#skF_5', B_2321), B_2322, '#skF_6'), k1_xboole_0) | ~r2_hidden('#skF_1'('#skF_5', B_2321), k2_relat_1('#skF_6')) | r1_xboole_0('#skF_5', B_2321) | ~r2_hidden('#skF_1'('#skF_5', B_2321), k9_relat_1('#skF_6', B_2322)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_46523])).
% 25.20/16.97  tff(c_46594, plain, (![B_2324, B_2325]: (~r2_hidden('#skF_1'('#skF_5', B_2324), k2_relat_1('#skF_6')) | r1_xboole_0('#skF_5', B_2324) | ~r2_hidden('#skF_1'('#skF_5', B_2324), k9_relat_1('#skF_6', B_2325)))), inference(negUnitSimplification, [status(thm)], [c_86, c_46592])).
% 25.20/16.97  tff(c_46704, plain, (![B_2324]: (~r2_hidden('#skF_1'('#skF_5', B_2324), k2_relat_1('#skF_6')) | r1_xboole_0('#skF_5', B_2324) | ~r2_hidden('#skF_1'('#skF_5', B_2324), k2_relat_1('#skF_6')) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_46594])).
% 25.20/16.97  tff(c_46758, plain, (![B_2326]: (r1_xboole_0('#skF_5', B_2326) | ~r2_hidden('#skF_1'('#skF_5', B_2326), k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_46704])).
% 25.20/16.97  tff(c_46794, plain, (r1_xboole_0('#skF_5', k2_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_6, c_46758])).
% 25.20/16.97  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 25.20/16.97  tff(c_46798, plain, (r1_xboole_0(k2_relat_1('#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_46794, c_2])).
% 25.20/16.97  tff(c_46803, plain, $false, inference(negUnitSimplification, [status(thm)], [c_704, c_46798])).
% 25.20/16.97  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 25.20/16.97  
% 25.20/16.97  Inference rules
% 25.20/16.97  ----------------------
% 25.20/16.97  #Ref     : 0
% 25.20/16.97  #Sup     : 11247
% 25.20/16.97  #Fact    : 0
% 25.20/16.97  #Define  : 0
% 25.20/16.97  #Split   : 8
% 25.20/16.97  #Chain   : 0
% 25.20/16.97  #Close   : 0
% 25.20/16.97  
% 25.20/16.97  Ordering : KBO
% 25.20/16.97  
% 25.20/16.97  Simplification rules
% 25.20/16.97  ----------------------
% 25.20/16.97  #Subsume      : 4765
% 25.20/16.97  #Demod        : 4302
% 25.20/16.97  #Tautology    : 2022
% 25.20/16.97  #SimpNegUnit  : 187
% 25.20/16.97  #BackRed      : 0
% 25.20/16.97  
% 25.20/16.97  #Partial instantiations: 0
% 25.20/16.97  #Strategies tried      : 1
% 25.20/16.97  
% 25.20/16.97  Timing (in seconds)
% 25.20/16.97  ----------------------
% 25.20/16.97  Preprocessing        : 0.34
% 25.20/16.97  Parsing              : 0.18
% 25.20/16.97  CNF conversion       : 0.02
% 25.20/16.97  Main loop            : 15.85
% 25.20/16.97  Inferencing          : 1.91
% 25.20/16.97  Reduction            : 1.76
% 25.20/16.97  Demodulation         : 1.18
% 25.20/16.97  BG Simplification    : 0.14
% 25.20/16.97  Subsumption          : 11.65
% 25.20/16.97  Abstraction          : 0.22
% 25.20/16.97  MUC search           : 0.00
% 25.20/16.97  Cooper               : 0.00
% 25.20/16.97  Total                : 16.22
% 25.20/16.97  Index Insertion      : 0.00
% 25.20/16.97  Index Deletion       : 0.00
% 25.20/16.97  Index Matching       : 0.00
% 25.20/16.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
