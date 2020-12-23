%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:13 EST 2020

% Result     : Theorem 12.15s
% Output     : CNFRefutation 12.15s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 135 expanded)
%              Number of leaves         :   25 (  59 expanded)
%              Depth                    :   12
%              Number of atoms          :   97 ( 313 expanded)
%              Number of equality atoms :   14 (  40 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_setfam_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v3_setfam_1,type,(
    v3_setfam_1: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_76,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( v3_setfam_1(B,A)
              & m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A))) )
           => ! [C] :
                ( ( v3_setfam_1(C,A)
                  & m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A))) )
               => v3_setfam_1(k4_subset_1(k1_zfmisc_1(A),B,C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_setfam_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v3_setfam_1(B,A)
      <=> ~ r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_setfam_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(c_42,plain,(
    v3_setfam_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_121,plain,(
    ! [A_48,B_49] :
      ( ~ r2_hidden(A_48,B_49)
      | ~ v3_setfam_1(B_49,A_48)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(k1_zfmisc_1(A_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_124,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | ~ v3_setfam_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_121])).

tff(c_130,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_124])).

tff(c_38,plain,(
    v3_setfam_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_127,plain,
    ( ~ r2_hidden('#skF_3','#skF_5')
    | ~ v3_setfam_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_121])).

tff(c_133,plain,(
    ~ r2_hidden('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_127])).

tff(c_134,plain,(
    ! [A_50,B_51,C_52] :
      ( k4_subset_1(A_50,B_51,C_52) = k2_xboole_0(B_51,C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(A_50))
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_183,plain,(
    ! [B_67] :
      ( k4_subset_1(k1_zfmisc_1('#skF_3'),B_67,'#skF_5') = k2_xboole_0(B_67,'#skF_5')
      | ~ m1_subset_1(B_67,k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_36,c_134])).

tff(c_190,plain,(
    k4_subset_1(k1_zfmisc_1('#skF_3'),'#skF_4','#skF_5') = k2_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_183])).

tff(c_34,plain,(
    ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1('#skF_3'),'#skF_4','#skF_5'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_264,plain,(
    ~ v3_setfam_1(k2_xboole_0('#skF_4','#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_34])).

tff(c_26,plain,(
    ! [A_14,B_15,C_16] :
      ( m1_subset_1(k4_subset_1(A_14,B_15,C_16),k1_zfmisc_1(A_14))
      | ~ m1_subset_1(C_16,k1_zfmisc_1(A_14))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_268,plain,
    ( m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1(k1_zfmisc_1('#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_26])).

tff(c_272,plain,(
    m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_268])).

tff(c_30,plain,(
    ! [B_21,A_20] :
      ( v3_setfam_1(B_21,A_20)
      | r2_hidden(A_20,B_21)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k1_zfmisc_1(A_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_287,plain,
    ( v3_setfam_1(k2_xboole_0('#skF_4','#skF_5'),'#skF_3')
    | r2_hidden('#skF_3',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_272,c_30])).

tff(c_294,plain,(
    r2_hidden('#skF_3',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_264,c_287])).

tff(c_2,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,k4_xboole_0(A_1,B_2))
      | r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    ! [A_7,B_8,C_9] : k4_xboole_0(k4_xboole_0(A_7,B_8),C_9) = k4_xboole_0(A_7,k2_xboole_0(B_8,C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_104,plain,(
    ! [D_45,A_46,B_47] :
      ( r2_hidden(D_45,k4_xboole_0(A_46,B_47))
      | r2_hidden(D_45,B_47)
      | ~ r2_hidden(D_45,A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20653,plain,(
    ! [D_711,A_712,B_713,C_714] :
      ( r2_hidden(D_711,k4_xboole_0(A_712,k2_xboole_0(B_713,C_714)))
      | r2_hidden(D_711,C_714)
      | ~ r2_hidden(D_711,k4_xboole_0(A_712,B_713)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_104])).

tff(c_15017,plain,(
    ! [A_510,B_511,C_512] :
      ( r2_hidden('#skF_1'(A_510,B_511,C_512),A_510)
      | r2_hidden('#skF_2'(A_510,B_511,C_512),C_512)
      | k4_xboole_0(A_510,B_511) = C_512 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_15083,plain,(
    ! [A_513,C_514] :
      ( r2_hidden('#skF_2'(A_513,A_513,C_514),C_514)
      | k4_xboole_0(A_513,A_513) = C_514 ) ),
    inference(resolution,[status(thm)],[c_15017,c_16])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_15110,plain,(
    ! [A_513,A_1,B_2] :
      ( r2_hidden('#skF_2'(A_513,A_513,k4_xboole_0(A_1,B_2)),A_1)
      | k4_xboole_0(A_513,A_513) = k4_xboole_0(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_15083,c_6])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20384,plain,(
    ! [A_699,A_700,B_701] :
      ( ~ r2_hidden('#skF_2'(A_699,A_699,k4_xboole_0(A_700,B_701)),B_701)
      | k4_xboole_0(A_700,B_701) = k4_xboole_0(A_699,A_699) ) ),
    inference(resolution,[status(thm)],[c_15083,c_4])).

tff(c_20415,plain,(
    ! [A_703,A_702] : k4_xboole_0(A_703,A_703) = k4_xboole_0(A_702,A_702) ),
    inference(resolution,[status(thm)],[c_15110,c_20384])).

tff(c_65,plain,(
    ! [A_36,B_37,C_38] : k4_xboole_0(k4_xboole_0(A_36,B_37),C_38) = k4_xboole_0(A_36,k2_xboole_0(B_37,C_38)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_88,plain,(
    ! [D_39,C_40,A_41,B_42] :
      ( ~ r2_hidden(D_39,C_40)
      | ~ r2_hidden(D_39,k4_xboole_0(A_41,k2_xboole_0(B_42,C_40))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_4])).

tff(c_92,plain,(
    ! [D_39,A_7,B_42,B_8,C_40] :
      ( ~ r2_hidden(D_39,C_40)
      | ~ r2_hidden(D_39,k4_xboole_0(A_7,k2_xboole_0(B_8,k2_xboole_0(B_42,C_40)))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_88])).

tff(c_20526,plain,(
    ! [D_704,C_705,A_706] :
      ( ~ r2_hidden(D_704,C_705)
      | ~ r2_hidden(D_704,k4_xboole_0(A_706,A_706)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20415,c_92])).

tff(c_20570,plain,(
    ! [A_706] : ~ r2_hidden('#skF_3',k4_xboole_0(A_706,A_706)) ),
    inference(resolution,[status(thm)],[c_294,c_20526])).

tff(c_23273,plain,(
    ! [C_759,B_760] :
      ( r2_hidden('#skF_3',C_759)
      | ~ r2_hidden('#skF_3',k4_xboole_0(k2_xboole_0(B_760,C_759),B_760)) ) ),
    inference(resolution,[status(thm)],[c_20653,c_20570])).

tff(c_24175,plain,(
    ! [C_783,B_784] :
      ( r2_hidden('#skF_3',C_783)
      | r2_hidden('#skF_3',B_784)
      | ~ r2_hidden('#skF_3',k2_xboole_0(B_784,C_783)) ) ),
    inference(resolution,[status(thm)],[c_2,c_23273])).

tff(c_24198,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_294,c_24175])).

tff(c_24208,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_133,c_24198])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:27:29 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.15/4.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.15/4.71  
% 12.15/4.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.15/4.72  %$ v3_setfam_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 12.15/4.72  
% 12.15/4.72  %Foreground sorts:
% 12.15/4.72  
% 12.15/4.72  
% 12.15/4.72  %Background operators:
% 12.15/4.72  
% 12.15/4.72  
% 12.15/4.72  %Foreground operators:
% 12.15/4.72  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 12.15/4.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.15/4.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.15/4.72  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.15/4.72  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.15/4.72  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 12.15/4.72  tff('#skF_5', type, '#skF_5': $i).
% 12.15/4.72  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 12.15/4.72  tff('#skF_3', type, '#skF_3': $i).
% 12.15/4.72  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 12.15/4.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.15/4.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.15/4.72  tff(k3_tarski, type, k3_tarski: $i > $i).
% 12.15/4.72  tff('#skF_4', type, '#skF_4': $i).
% 12.15/4.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.15/4.72  tff(v3_setfam_1, type, v3_setfam_1: ($i * $i) > $o).
% 12.15/4.72  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.15/4.72  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.15/4.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.15/4.72  
% 12.15/4.73  tff(f_76, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((v3_setfam_1(B, A) & m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A)))) => (![C]: ((v3_setfam_1(C, A) & m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A)))) => v3_setfam_1(k4_subset_1(k1_zfmisc_1(A), B, C), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_setfam_1)).
% 12.15/4.73  tff(f_60, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v3_setfam_1(B, A) <=> ~r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_setfam_1)).
% 12.15/4.73  tff(f_53, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 12.15/4.73  tff(f_47, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 12.15/4.73  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 12.15/4.73  tff(f_37, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 12.15/4.73  tff(c_42, plain, (v3_setfam_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 12.15/4.73  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 12.15/4.73  tff(c_121, plain, (![A_48, B_49]: (~r2_hidden(A_48, B_49) | ~v3_setfam_1(B_49, A_48) | ~m1_subset_1(B_49, k1_zfmisc_1(k1_zfmisc_1(A_48))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 12.15/4.73  tff(c_124, plain, (~r2_hidden('#skF_3', '#skF_4') | ~v3_setfam_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_121])).
% 12.15/4.73  tff(c_130, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_124])).
% 12.15/4.73  tff(c_38, plain, (v3_setfam_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 12.15/4.73  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 12.15/4.73  tff(c_127, plain, (~r2_hidden('#skF_3', '#skF_5') | ~v3_setfam_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_121])).
% 12.15/4.73  tff(c_133, plain, (~r2_hidden('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_127])).
% 12.15/4.73  tff(c_134, plain, (![A_50, B_51, C_52]: (k4_subset_1(A_50, B_51, C_52)=k2_xboole_0(B_51, C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(A_50)) | ~m1_subset_1(B_51, k1_zfmisc_1(A_50)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 12.15/4.73  tff(c_183, plain, (![B_67]: (k4_subset_1(k1_zfmisc_1('#skF_3'), B_67, '#skF_5')=k2_xboole_0(B_67, '#skF_5') | ~m1_subset_1(B_67, k1_zfmisc_1(k1_zfmisc_1('#skF_3'))))), inference(resolution, [status(thm)], [c_36, c_134])).
% 12.15/4.73  tff(c_190, plain, (k4_subset_1(k1_zfmisc_1('#skF_3'), '#skF_4', '#skF_5')=k2_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_40, c_183])).
% 12.15/4.73  tff(c_34, plain, (~v3_setfam_1(k4_subset_1(k1_zfmisc_1('#skF_3'), '#skF_4', '#skF_5'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 12.15/4.73  tff(c_264, plain, (~v3_setfam_1(k2_xboole_0('#skF_4', '#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_190, c_34])).
% 12.15/4.73  tff(c_26, plain, (![A_14, B_15, C_16]: (m1_subset_1(k4_subset_1(A_14, B_15, C_16), k1_zfmisc_1(A_14)) | ~m1_subset_1(C_16, k1_zfmisc_1(A_14)) | ~m1_subset_1(B_15, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.15/4.73  tff(c_268, plain, (m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_190, c_26])).
% 12.15/4.73  tff(c_272, plain, (m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_268])).
% 12.15/4.73  tff(c_30, plain, (![B_21, A_20]: (v3_setfam_1(B_21, A_20) | r2_hidden(A_20, B_21) | ~m1_subset_1(B_21, k1_zfmisc_1(k1_zfmisc_1(A_20))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 12.15/4.73  tff(c_287, plain, (v3_setfam_1(k2_xboole_0('#skF_4', '#skF_5'), '#skF_3') | r2_hidden('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_272, c_30])).
% 12.15/4.73  tff(c_294, plain, (r2_hidden('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_264, c_287])).
% 12.15/4.73  tff(c_2, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, k4_xboole_0(A_1, B_2)) | r2_hidden(D_6, B_2) | ~r2_hidden(D_6, A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.15/4.73  tff(c_20, plain, (![A_7, B_8, C_9]: (k4_xboole_0(k4_xboole_0(A_7, B_8), C_9)=k4_xboole_0(A_7, k2_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.15/4.73  tff(c_104, plain, (![D_45, A_46, B_47]: (r2_hidden(D_45, k4_xboole_0(A_46, B_47)) | r2_hidden(D_45, B_47) | ~r2_hidden(D_45, A_46))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.15/4.73  tff(c_20653, plain, (![D_711, A_712, B_713, C_714]: (r2_hidden(D_711, k4_xboole_0(A_712, k2_xboole_0(B_713, C_714))) | r2_hidden(D_711, C_714) | ~r2_hidden(D_711, k4_xboole_0(A_712, B_713)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_104])).
% 12.15/4.73  tff(c_15017, plain, (![A_510, B_511, C_512]: (r2_hidden('#skF_1'(A_510, B_511, C_512), A_510) | r2_hidden('#skF_2'(A_510, B_511, C_512), C_512) | k4_xboole_0(A_510, B_511)=C_512)), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.15/4.73  tff(c_16, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.15/4.73  tff(c_15083, plain, (![A_513, C_514]: (r2_hidden('#skF_2'(A_513, A_513, C_514), C_514) | k4_xboole_0(A_513, A_513)=C_514)), inference(resolution, [status(thm)], [c_15017, c_16])).
% 12.15/4.73  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.15/4.73  tff(c_15110, plain, (![A_513, A_1, B_2]: (r2_hidden('#skF_2'(A_513, A_513, k4_xboole_0(A_1, B_2)), A_1) | k4_xboole_0(A_513, A_513)=k4_xboole_0(A_1, B_2))), inference(resolution, [status(thm)], [c_15083, c_6])).
% 12.15/4.73  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.15/4.73  tff(c_20384, plain, (![A_699, A_700, B_701]: (~r2_hidden('#skF_2'(A_699, A_699, k4_xboole_0(A_700, B_701)), B_701) | k4_xboole_0(A_700, B_701)=k4_xboole_0(A_699, A_699))), inference(resolution, [status(thm)], [c_15083, c_4])).
% 12.15/4.73  tff(c_20415, plain, (![A_703, A_702]: (k4_xboole_0(A_703, A_703)=k4_xboole_0(A_702, A_702))), inference(resolution, [status(thm)], [c_15110, c_20384])).
% 12.15/4.73  tff(c_65, plain, (![A_36, B_37, C_38]: (k4_xboole_0(k4_xboole_0(A_36, B_37), C_38)=k4_xboole_0(A_36, k2_xboole_0(B_37, C_38)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.15/4.73  tff(c_88, plain, (![D_39, C_40, A_41, B_42]: (~r2_hidden(D_39, C_40) | ~r2_hidden(D_39, k4_xboole_0(A_41, k2_xboole_0(B_42, C_40))))), inference(superposition, [status(thm), theory('equality')], [c_65, c_4])).
% 12.15/4.73  tff(c_92, plain, (![D_39, A_7, B_42, B_8, C_40]: (~r2_hidden(D_39, C_40) | ~r2_hidden(D_39, k4_xboole_0(A_7, k2_xboole_0(B_8, k2_xboole_0(B_42, C_40)))))), inference(superposition, [status(thm), theory('equality')], [c_20, c_88])).
% 12.15/4.73  tff(c_20526, plain, (![D_704, C_705, A_706]: (~r2_hidden(D_704, C_705) | ~r2_hidden(D_704, k4_xboole_0(A_706, A_706)))), inference(superposition, [status(thm), theory('equality')], [c_20415, c_92])).
% 12.15/4.73  tff(c_20570, plain, (![A_706]: (~r2_hidden('#skF_3', k4_xboole_0(A_706, A_706)))), inference(resolution, [status(thm)], [c_294, c_20526])).
% 12.15/4.73  tff(c_23273, plain, (![C_759, B_760]: (r2_hidden('#skF_3', C_759) | ~r2_hidden('#skF_3', k4_xboole_0(k2_xboole_0(B_760, C_759), B_760)))), inference(resolution, [status(thm)], [c_20653, c_20570])).
% 12.15/4.73  tff(c_24175, plain, (![C_783, B_784]: (r2_hidden('#skF_3', C_783) | r2_hidden('#skF_3', B_784) | ~r2_hidden('#skF_3', k2_xboole_0(B_784, C_783)))), inference(resolution, [status(thm)], [c_2, c_23273])).
% 12.15/4.73  tff(c_24198, plain, (r2_hidden('#skF_3', '#skF_5') | r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_294, c_24175])).
% 12.15/4.73  tff(c_24208, plain, $false, inference(negUnitSimplification, [status(thm)], [c_130, c_133, c_24198])).
% 12.15/4.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.15/4.73  
% 12.15/4.73  Inference rules
% 12.15/4.73  ----------------------
% 12.15/4.73  #Ref     : 0
% 12.15/4.73  #Sup     : 6445
% 12.15/4.73  #Fact    : 10
% 12.15/4.73  #Define  : 0
% 12.15/4.73  #Split   : 6
% 12.15/4.73  #Chain   : 0
% 12.15/4.73  #Close   : 0
% 12.15/4.73  
% 12.15/4.73  Ordering : KBO
% 12.15/4.73  
% 12.15/4.73  Simplification rules
% 12.15/4.73  ----------------------
% 12.15/4.73  #Subsume      : 1882
% 12.15/4.73  #Demod        : 3554
% 12.15/4.73  #Tautology    : 328
% 12.15/4.73  #SimpNegUnit  : 42
% 12.15/4.73  #BackRed      : 5
% 12.15/4.73  
% 12.15/4.73  #Partial instantiations: 0
% 12.15/4.73  #Strategies tried      : 1
% 12.15/4.73  
% 12.15/4.73  Timing (in seconds)
% 12.15/4.73  ----------------------
% 12.15/4.73  Preprocessing        : 0.39
% 12.15/4.73  Parsing              : 0.19
% 12.15/4.73  CNF conversion       : 0.03
% 12.15/4.73  Main loop            : 3.54
% 12.15/4.73  Inferencing          : 0.88
% 12.15/4.73  Reduction            : 1.53
% 12.15/4.73  Demodulation         : 1.25
% 12.15/4.73  BG Simplification    : 0.13
% 12.15/4.73  Subsumption          : 0.79
% 12.15/4.73  Abstraction          : 0.17
% 12.15/4.73  MUC search           : 0.00
% 12.15/4.73  Cooper               : 0.00
% 12.15/4.73  Total                : 3.96
% 12.15/4.73  Index Insertion      : 0.00
% 12.15/4.74  Index Deletion       : 0.00
% 12.15/4.74  Index Matching       : 0.00
% 12.15/4.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
