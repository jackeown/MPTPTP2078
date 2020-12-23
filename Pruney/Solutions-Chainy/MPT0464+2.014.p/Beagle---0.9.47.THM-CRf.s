%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:45 EST 2020

% Result     : Theorem 3.73s
% Output     : CNFRefutation 3.73s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 126 expanded)
%              Number of leaves         :   39 (  59 expanded)
%              Depth                    :    9
%              Number of atoms          :  118 ( 237 expanded)
%              Number of equality atoms :   24 (  26 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_41,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_81,axiom,(
    ! [A,B,C,D,E,F,G,H,I] :
      ( I = k6_enumset1(A,B,C,D,E,F,G,H)
    <=> ! [J] :
          ( r2_hidden(J,I)
        <=> ~ ( J != A
              & J != B
              & J != C
              & J != D
              & J != E
              & J != F
              & J != G
              & J != H ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_enumset1)).

tff(f_83,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_126,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( v1_relat_1(C)
               => r1_tarski(k5_relat_1(A,k3_xboole_0(B,C)),k3_xboole_0(k5_relat_1(A,B),k5_relat_1(A,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relat_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_98,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_115,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ! [D] :
                  ( v1_relat_1(D)
                 => ( ( r1_tarski(A,B)
                      & r1_tarski(C,D) )
                   => r1_tarski(k5_relat_1(A,C),k5_relat_1(B,D)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relat_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_12,plain,(
    ! [A_8,B_9] : k1_enumset1(A_8,A_8,B_9) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [A_10,B_11,C_12] : k2_enumset1(A_10,A_10,B_11,C_12) = k1_enumset1(A_10,B_11,C_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_13,B_14,C_15,D_16] : k3_enumset1(A_13,A_13,B_14,C_15,D_16) = k2_enumset1(A_13,B_14,C_15,D_16) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    ! [E_21,D_20,C_19,B_18,A_17] : k4_enumset1(A_17,A_17,B_18,C_19,D_20,E_21) = k3_enumset1(A_17,B_18,C_19,D_20,E_21) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_20,plain,(
    ! [E_26,F_27,A_22,B_23,D_25,C_24] : k5_enumset1(A_22,A_22,B_23,C_24,D_25,E_26,F_27) = k4_enumset1(A_22,B_23,C_24,D_25,E_26,F_27) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_857,plain,(
    ! [D_379,E_375,B_378,G_373,F_374,C_377,A_376] : k6_enumset1(A_376,A_376,B_378,C_377,D_379,E_375,F_374,G_373) = k5_enumset1(A_376,B_378,C_377,D_379,E_375,F_374,G_373) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_26,plain,(
    ! [A_35,F_40,B_36,C_37,D_38,J_46,E_39,G_41] : r2_hidden(J_46,k6_enumset1(A_35,B_36,C_37,D_38,E_39,F_40,G_41,J_46)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1167,plain,(
    ! [F_452,G_449,E_455,D_450,A_453,B_454,C_451] : r2_hidden(G_449,k5_enumset1(A_453,B_454,C_451,D_450,E_455,F_452,G_449)) ),
    inference(superposition,[status(thm),theory(equality)],[c_857,c_26])).

tff(c_1178,plain,(
    ! [C_457,D_460,F_459,E_458,B_461,A_456] : r2_hidden(F_459,k4_enumset1(A_456,B_461,C_457,D_460,E_458,F_459)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1167])).

tff(c_1189,plain,(
    ! [B_464,D_465,E_466,A_463,C_462] : r2_hidden(E_466,k3_enumset1(A_463,B_464,C_462,D_465,E_466)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1178])).

tff(c_1200,plain,(
    ! [D_467,A_468,B_469,C_470] : r2_hidden(D_467,k2_enumset1(A_468,B_469,C_470,D_467)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1189])).

tff(c_1212,plain,(
    ! [C_480,A_481,B_482] : r2_hidden(C_480,k1_enumset1(A_481,B_482,C_480)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1200])).

tff(c_1223,plain,(
    ! [B_483,A_484] : r2_hidden(B_483,k2_tarski(A_484,B_483)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1212])).

tff(c_102,plain,(
    ! [A_82,B_83] : k1_setfam_1(k2_tarski(A_82,B_83)) = k3_xboole_0(A_82,B_83) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_84,plain,(
    ! [B_52,A_51] :
      ( r1_tarski(k1_setfam_1(B_52),A_51)
      | ~ r2_hidden(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_108,plain,(
    ! [A_82,B_83,A_51] :
      ( r1_tarski(k3_xboole_0(A_82,B_83),A_51)
      | ~ r2_hidden(A_51,k2_tarski(A_82,B_83)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_84])).

tff(c_1242,plain,(
    ! [A_484,B_483] : r1_tarski(k3_xboole_0(A_484,B_483),B_483) ),
    inference(resolution,[status(thm)],[c_1223,c_108])).

tff(c_94,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_82,plain,(
    ! [A_49,B_50] :
      ( m1_subset_1(A_49,k1_zfmisc_1(B_50))
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_141,plain,(
    ! [B_90,A_91] :
      ( v1_relat_1(B_90)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(A_91))
      | ~ v1_relat_1(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_146,plain,(
    ! [A_92,B_93] :
      ( v1_relat_1(A_92)
      | ~ v1_relat_1(B_93)
      | ~ r1_tarski(A_92,B_93) ) ),
    inference(resolution,[status(thm)],[c_82,c_141])).

tff(c_157,plain,(
    ! [A_3,B_4] :
      ( v1_relat_1(k3_xboole_0(A_3,B_4))
      | ~ v1_relat_1(A_3) ) ),
    inference(resolution,[status(thm)],[c_8,c_146])).

tff(c_96,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_92,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_999,plain,(
    ! [A_410,C_411,B_412,D_413] :
      ( r1_tarski(k5_relat_1(A_410,C_411),k5_relat_1(B_412,D_413))
      | ~ r1_tarski(C_411,D_413)
      | ~ r1_tarski(A_410,B_412)
      | ~ v1_relat_1(D_413)
      | ~ v1_relat_1(C_411)
      | ~ v1_relat_1(B_412)
      | ~ v1_relat_1(A_410) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_650,plain,(
    ! [A_287,C_288,B_289,D_290] :
      ( r1_tarski(k5_relat_1(A_287,C_288),k5_relat_1(B_289,D_290))
      | ~ r1_tarski(C_288,D_290)
      | ~ r1_tarski(A_287,B_289)
      | ~ v1_relat_1(D_290)
      | ~ v1_relat_1(C_288)
      | ~ v1_relat_1(B_289)
      | ~ v1_relat_1(A_287) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_239,plain,(
    ! [A_176,B_177,C_178] :
      ( r1_tarski(A_176,k3_xboole_0(B_177,C_178))
      | ~ r1_tarski(A_176,C_178)
      | ~ r1_tarski(A_176,B_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_90,plain,(
    ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k3_xboole_0(k5_relat_1('#skF_3','#skF_4'),k5_relat_1('#skF_3','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_257,plain,
    ( ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_5'))
    | ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_239,c_90])).

tff(c_445,plain,(
    ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_257])).

tff(c_653,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_4')
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_650,c_445])).

tff(c_664,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_6,c_8,c_653])).

tff(c_670,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_157,c_664])).

tff(c_674,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_670])).

tff(c_675,plain,(
    ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_257])).

tff(c_1005,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_5')
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_999,c_675])).

tff(c_1019,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_5')
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_92,c_6,c_1005])).

tff(c_1023,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1019])).

tff(c_1026,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_157,c_1023])).

tff(c_1030,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_1026])).

tff(c_1031,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_1019])).

tff(c_1247,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1242,c_1031])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:19:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.73/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.73/1.57  
% 3.73/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.73/1.57  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.73/1.57  
% 3.73/1.57  %Foreground sorts:
% 3.73/1.57  
% 3.73/1.57  
% 3.73/1.57  %Background operators:
% 3.73/1.57  
% 3.73/1.57  
% 3.73/1.57  %Foreground operators:
% 3.73/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.73/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.73/1.57  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.73/1.57  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.73/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.73/1.57  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.73/1.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.73/1.57  tff('#skF_5', type, '#skF_5': $i).
% 3.73/1.57  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.73/1.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.73/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.73/1.57  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.73/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.73/1.57  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.73/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.73/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.73/1.57  tff('#skF_4', type, '#skF_4': $i).
% 3.73/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.73/1.57  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.73/1.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.73/1.57  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.73/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.73/1.57  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.73/1.57  
% 3.73/1.59  tff(f_41, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.73/1.59  tff(f_43, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.73/1.59  tff(f_45, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 3.73/1.59  tff(f_47, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 3.73/1.59  tff(f_49, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 3.73/1.59  tff(f_51, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 3.73/1.59  tff(f_81, axiom, (![A, B, C, D, E, F, G, H, I]: ((I = k6_enumset1(A, B, C, D, E, F, G, H)) <=> (![J]: (r2_hidden(J, I) <=> ~(((((((~(J = A) & ~(J = B)) & ~(J = C)) & ~(J = D)) & ~(J = E)) & ~(J = F)) & ~(J = G)) & ~(J = H)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_enumset1)).
% 3.73/1.59  tff(f_83, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.73/1.59  tff(f_91, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 3.73/1.59  tff(f_126, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => r1_tarski(k5_relat_1(A, k3_xboole_0(B, C)), k3_xboole_0(k5_relat_1(A, B), k5_relat_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_relat_1)).
% 3.73/1.59  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.73/1.59  tff(f_87, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.73/1.59  tff(f_98, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.73/1.59  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.73/1.59  tff(f_115, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k5_relat_1(A, C), k5_relat_1(B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_relat_1)).
% 3.73/1.59  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 3.73/1.59  tff(c_12, plain, (![A_8, B_9]: (k1_enumset1(A_8, A_8, B_9)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.73/1.59  tff(c_14, plain, (![A_10, B_11, C_12]: (k2_enumset1(A_10, A_10, B_11, C_12)=k1_enumset1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.73/1.59  tff(c_16, plain, (![A_13, B_14, C_15, D_16]: (k3_enumset1(A_13, A_13, B_14, C_15, D_16)=k2_enumset1(A_13, B_14, C_15, D_16))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.73/1.59  tff(c_18, plain, (![E_21, D_20, C_19, B_18, A_17]: (k4_enumset1(A_17, A_17, B_18, C_19, D_20, E_21)=k3_enumset1(A_17, B_18, C_19, D_20, E_21))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.73/1.59  tff(c_20, plain, (![E_26, F_27, A_22, B_23, D_25, C_24]: (k5_enumset1(A_22, A_22, B_23, C_24, D_25, E_26, F_27)=k4_enumset1(A_22, B_23, C_24, D_25, E_26, F_27))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.73/1.59  tff(c_857, plain, (![D_379, E_375, B_378, G_373, F_374, C_377, A_376]: (k6_enumset1(A_376, A_376, B_378, C_377, D_379, E_375, F_374, G_373)=k5_enumset1(A_376, B_378, C_377, D_379, E_375, F_374, G_373))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.73/1.59  tff(c_26, plain, (![A_35, F_40, B_36, C_37, D_38, J_46, E_39, G_41]: (r2_hidden(J_46, k6_enumset1(A_35, B_36, C_37, D_38, E_39, F_40, G_41, J_46)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.73/1.59  tff(c_1167, plain, (![F_452, G_449, E_455, D_450, A_453, B_454, C_451]: (r2_hidden(G_449, k5_enumset1(A_453, B_454, C_451, D_450, E_455, F_452, G_449)))), inference(superposition, [status(thm), theory('equality')], [c_857, c_26])).
% 3.73/1.59  tff(c_1178, plain, (![C_457, D_460, F_459, E_458, B_461, A_456]: (r2_hidden(F_459, k4_enumset1(A_456, B_461, C_457, D_460, E_458, F_459)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1167])).
% 3.73/1.59  tff(c_1189, plain, (![B_464, D_465, E_466, A_463, C_462]: (r2_hidden(E_466, k3_enumset1(A_463, B_464, C_462, D_465, E_466)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1178])).
% 3.73/1.59  tff(c_1200, plain, (![D_467, A_468, B_469, C_470]: (r2_hidden(D_467, k2_enumset1(A_468, B_469, C_470, D_467)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1189])).
% 3.73/1.59  tff(c_1212, plain, (![C_480, A_481, B_482]: (r2_hidden(C_480, k1_enumset1(A_481, B_482, C_480)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1200])).
% 3.73/1.59  tff(c_1223, plain, (![B_483, A_484]: (r2_hidden(B_483, k2_tarski(A_484, B_483)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1212])).
% 3.73/1.59  tff(c_102, plain, (![A_82, B_83]: (k1_setfam_1(k2_tarski(A_82, B_83))=k3_xboole_0(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.73/1.59  tff(c_84, plain, (![B_52, A_51]: (r1_tarski(k1_setfam_1(B_52), A_51) | ~r2_hidden(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.73/1.59  tff(c_108, plain, (![A_82, B_83, A_51]: (r1_tarski(k3_xboole_0(A_82, B_83), A_51) | ~r2_hidden(A_51, k2_tarski(A_82, B_83)))), inference(superposition, [status(thm), theory('equality')], [c_102, c_84])).
% 3.73/1.59  tff(c_1242, plain, (![A_484, B_483]: (r1_tarski(k3_xboole_0(A_484, B_483), B_483))), inference(resolution, [status(thm)], [c_1223, c_108])).
% 3.73/1.59  tff(c_94, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.73/1.59  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.73/1.59  tff(c_82, plain, (![A_49, B_50]: (m1_subset_1(A_49, k1_zfmisc_1(B_50)) | ~r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.73/1.59  tff(c_141, plain, (![B_90, A_91]: (v1_relat_1(B_90) | ~m1_subset_1(B_90, k1_zfmisc_1(A_91)) | ~v1_relat_1(A_91))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.73/1.59  tff(c_146, plain, (![A_92, B_93]: (v1_relat_1(A_92) | ~v1_relat_1(B_93) | ~r1_tarski(A_92, B_93))), inference(resolution, [status(thm)], [c_82, c_141])).
% 3.73/1.59  tff(c_157, plain, (![A_3, B_4]: (v1_relat_1(k3_xboole_0(A_3, B_4)) | ~v1_relat_1(A_3))), inference(resolution, [status(thm)], [c_8, c_146])).
% 3.73/1.59  tff(c_96, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.73/1.59  tff(c_92, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.73/1.59  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.73/1.59  tff(c_999, plain, (![A_410, C_411, B_412, D_413]: (r1_tarski(k5_relat_1(A_410, C_411), k5_relat_1(B_412, D_413)) | ~r1_tarski(C_411, D_413) | ~r1_tarski(A_410, B_412) | ~v1_relat_1(D_413) | ~v1_relat_1(C_411) | ~v1_relat_1(B_412) | ~v1_relat_1(A_410))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.73/1.59  tff(c_650, plain, (![A_287, C_288, B_289, D_290]: (r1_tarski(k5_relat_1(A_287, C_288), k5_relat_1(B_289, D_290)) | ~r1_tarski(C_288, D_290) | ~r1_tarski(A_287, B_289) | ~v1_relat_1(D_290) | ~v1_relat_1(C_288) | ~v1_relat_1(B_289) | ~v1_relat_1(A_287))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.73/1.59  tff(c_239, plain, (![A_176, B_177, C_178]: (r1_tarski(A_176, k3_xboole_0(B_177, C_178)) | ~r1_tarski(A_176, C_178) | ~r1_tarski(A_176, B_177))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.73/1.59  tff(c_90, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k3_xboole_0(k5_relat_1('#skF_3', '#skF_4'), k5_relat_1('#skF_3', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.73/1.59  tff(c_257, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_5')) | ~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_239, c_90])).
% 3.73/1.59  tff(c_445, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_257])).
% 3.73/1.59  tff(c_653, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_4') | ~r1_tarski('#skF_3', '#skF_3') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_650, c_445])).
% 3.73/1.59  tff(c_664, plain, (~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_94, c_6, c_8, c_653])).
% 3.73/1.59  tff(c_670, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_157, c_664])).
% 3.73/1.59  tff(c_674, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_670])).
% 3.73/1.59  tff(c_675, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_257])).
% 3.73/1.59  tff(c_1005, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_5') | ~r1_tarski('#skF_3', '#skF_3') | ~v1_relat_1('#skF_5') | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_999, c_675])).
% 3.73/1.59  tff(c_1019, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_5') | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_92, c_6, c_1005])).
% 3.73/1.59  tff(c_1023, plain, (~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_1019])).
% 3.73/1.59  tff(c_1026, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_157, c_1023])).
% 3.73/1.59  tff(c_1030, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_1026])).
% 3.73/1.59  tff(c_1031, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_5')), inference(splitRight, [status(thm)], [c_1019])).
% 3.73/1.59  tff(c_1247, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1242, c_1031])).
% 3.73/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.73/1.59  
% 3.73/1.59  Inference rules
% 3.73/1.59  ----------------------
% 3.73/1.59  #Ref     : 0
% 3.73/1.59  #Sup     : 275
% 3.73/1.59  #Fact    : 0
% 3.73/1.59  #Define  : 0
% 3.73/1.59  #Split   : 4
% 3.73/1.59  #Chain   : 0
% 3.73/1.59  #Close   : 0
% 3.73/1.59  
% 3.73/1.59  Ordering : KBO
% 3.73/1.59  
% 3.73/1.59  Simplification rules
% 3.73/1.59  ----------------------
% 3.73/1.59  #Subsume      : 37
% 3.73/1.59  #Demod        : 73
% 3.73/1.59  #Tautology    : 89
% 3.73/1.59  #SimpNegUnit  : 0
% 3.73/1.59  #BackRed      : 1
% 3.73/1.59  
% 3.73/1.59  #Partial instantiations: 0
% 3.73/1.59  #Strategies tried      : 1
% 3.73/1.59  
% 3.73/1.59  Timing (in seconds)
% 3.73/1.59  ----------------------
% 3.73/1.59  Preprocessing        : 0.35
% 3.73/1.59  Parsing              : 0.17
% 3.73/1.59  CNF conversion       : 0.03
% 3.73/1.59  Main loop            : 0.47
% 3.73/1.59  Inferencing          : 0.16
% 3.73/1.59  Reduction            : 0.14
% 3.73/1.59  Demodulation         : 0.10
% 3.73/1.59  BG Simplification    : 0.03
% 3.73/1.59  Subsumption          : 0.12
% 3.73/1.59  Abstraction          : 0.04
% 3.73/1.59  MUC search           : 0.00
% 3.73/1.59  Cooper               : 0.00
% 3.73/1.59  Total                : 0.86
% 3.73/1.59  Index Insertion      : 0.00
% 3.73/1.59  Index Deletion       : 0.00
% 3.73/1.59  Index Matching       : 0.00
% 3.73/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
