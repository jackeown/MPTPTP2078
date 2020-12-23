%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:27 EST 2020

% Result     : Theorem 4.67s
% Output     : CNFRefutation 4.67s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 116 expanded)
%              Number of leaves         :   43 (  60 expanded)
%              Depth                    :   13
%              Number of atoms          :  102 ( 168 expanded)
%              Number of equality atoms :   18 (  32 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k1_enumset1 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_11 > #skF_6 > #skF_1 > #skF_15 > #skF_12 > #skF_4 > #skF_14 > #skF_13 > #skF_10 > #skF_2 > #skF_3 > #skF_8 > #skF_7 > #skF_9 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_15',type,(
    '#skF_15': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r2_hidden(k4_tarski(A,B),C)
         => ( r2_hidden(A,k3_relat_1(C))
            & r2_hidden(B,k3_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_51,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_69,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_53,axiom,(
    ! [A] : r1_tarski(A,k1_zfmisc_1(k3_tarski(A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_77,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_78,plain,
    ( ~ r2_hidden('#skF_14',k3_relat_1('#skF_15'))
    | ~ r2_hidden('#skF_13',k3_relat_1('#skF_15')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_101,plain,(
    ~ r2_hidden('#skF_13',k3_relat_1('#skF_15')) ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_82,plain,(
    v1_relat_1('#skF_15') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_76,plain,(
    ! [A_62] :
      ( k2_xboole_0(k1_relat_1(A_62),k2_relat_1(A_62)) = k3_relat_1(A_62)
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_42,plain,(
    ! [A_17,B_18] : k3_tarski(k2_tarski(A_17,B_18)) = k2_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_26,plain,(
    ! [D_14,B_10] : r2_hidden(D_14,k2_tarski(D_14,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_80,plain,(
    r2_hidden(k4_tarski('#skF_13','#skF_14'),'#skF_15') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_248,plain,(
    ! [C_108,A_109,D_110] :
      ( r2_hidden(C_108,k1_relat_1(A_109))
      | ~ r2_hidden(k4_tarski(C_108,D_110),A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_267,plain,(
    r2_hidden('#skF_13',k1_relat_1('#skF_15')) ),
    inference(resolution,[status(thm)],[c_80,c_248])).

tff(c_44,plain,(
    ! [A_19] : r1_tarski(A_19,k1_zfmisc_1(k3_tarski(A_19))) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_117,plain,(
    ! [A_80,B_81] :
      ( k3_xboole_0(A_80,B_81) = A_80
      | ~ r1_tarski(A_80,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_121,plain,(
    ! [A_19] : k3_xboole_0(A_19,k1_zfmisc_1(k3_tarski(A_19))) = A_19 ),
    inference(resolution,[status(thm)],[c_44,c_117])).

tff(c_150,plain,(
    ! [D_88,B_89,A_90] :
      ( r2_hidden(D_88,B_89)
      | ~ r2_hidden(D_88,k3_xboole_0(A_90,B_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_170,plain,(
    ! [D_96,A_97] :
      ( r2_hidden(D_96,k1_zfmisc_1(k3_tarski(A_97)))
      | ~ r2_hidden(D_96,A_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_150])).

tff(c_46,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(A_20,B_21)
      | ~ r2_hidden(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_178,plain,(
    ! [D_98,A_99] :
      ( m1_subset_1(D_98,k1_zfmisc_1(k3_tarski(A_99)))
      | ~ r2_hidden(D_98,A_99) ) ),
    inference(resolution,[status(thm)],[c_170,c_46])).

tff(c_48,plain,(
    ! [A_22,B_23] :
      ( r1_tarski(A_22,B_23)
      | ~ m1_subset_1(A_22,k1_zfmisc_1(B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_186,plain,(
    ! [D_100,A_101] :
      ( r1_tarski(D_100,k3_tarski(A_101))
      | ~ r2_hidden(D_100,A_101) ) ),
    inference(resolution,[status(thm)],[c_178,c_48])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_194,plain,(
    ! [D_102,A_103] :
      ( k3_xboole_0(D_102,k3_tarski(A_103)) = D_102
      | ~ r2_hidden(D_102,A_103) ) ),
    inference(resolution,[status(thm)],[c_186,c_20])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_669,plain,(
    ! [D_176,A_177,D_178] :
      ( r2_hidden(D_176,k3_tarski(A_177))
      | ~ r2_hidden(D_176,D_178)
      | ~ r2_hidden(D_178,A_177) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_4])).

tff(c_721,plain,(
    ! [A_179] :
      ( r2_hidden('#skF_13',k3_tarski(A_179))
      | ~ r2_hidden(k1_relat_1('#skF_15'),A_179) ) ),
    inference(resolution,[status(thm)],[c_267,c_669])).

tff(c_761,plain,(
    ! [B_10] : r2_hidden('#skF_13',k3_tarski(k2_tarski(k1_relat_1('#skF_15'),B_10))) ),
    inference(resolution,[status(thm)],[c_26,c_721])).

tff(c_782,plain,(
    ! [B_181] : r2_hidden('#skF_13',k2_xboole_0(k1_relat_1('#skF_15'),B_181)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_761])).

tff(c_791,plain,
    ( r2_hidden('#skF_13',k3_relat_1('#skF_15'))
    | ~ v1_relat_1('#skF_15') ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_782])).

tff(c_795,plain,(
    r2_hidden('#skF_13',k3_relat_1('#skF_15')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_791])).

tff(c_797,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_795])).

tff(c_798,plain,(
    ~ r2_hidden('#skF_14',k3_relat_1('#skF_15')) ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_24,plain,(
    ! [D_14,A_9] : r2_hidden(D_14,k2_tarski(A_9,D_14)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_877,plain,(
    ! [C_205,A_206,D_207] :
      ( r2_hidden(C_205,k2_relat_1(A_206))
      | ~ r2_hidden(k4_tarski(D_207,C_205),A_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_896,plain,(
    r2_hidden('#skF_14',k2_relat_1('#skF_15')) ),
    inference(resolution,[status(thm)],[c_80,c_877])).

tff(c_816,plain,(
    ! [A_184,B_185] :
      ( k3_xboole_0(A_184,B_185) = A_184
      | ~ r1_tarski(A_184,B_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_820,plain,(
    ! [A_19] : k3_xboole_0(A_19,k1_zfmisc_1(k3_tarski(A_19))) = A_19 ),
    inference(resolution,[status(thm)],[c_44,c_816])).

tff(c_848,plain,(
    ! [D_193,B_194,A_195] :
      ( r2_hidden(D_193,B_194)
      | ~ r2_hidden(D_193,k3_xboole_0(A_195,B_194)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_861,plain,(
    ! [D_201,A_202] :
      ( r2_hidden(D_201,k1_zfmisc_1(k3_tarski(A_202)))
      | ~ r2_hidden(D_201,A_202) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_820,c_848])).

tff(c_869,plain,(
    ! [D_203,A_204] :
      ( m1_subset_1(D_203,k1_zfmisc_1(k3_tarski(A_204)))
      | ~ r2_hidden(D_203,A_204) ) ),
    inference(resolution,[status(thm)],[c_861,c_46])).

tff(c_901,plain,(
    ! [D_208,A_209] :
      ( r1_tarski(D_208,k3_tarski(A_209))
      | ~ r2_hidden(D_208,A_209) ) ),
    inference(resolution,[status(thm)],[c_869,c_48])).

tff(c_942,plain,(
    ! [D_225,A_226] :
      ( k3_xboole_0(D_225,k3_tarski(A_226)) = D_225
      | ~ r2_hidden(D_225,A_226) ) ),
    inference(resolution,[status(thm)],[c_901,c_20])).

tff(c_1350,plain,(
    ! [D_281,A_282,D_283] :
      ( r2_hidden(D_281,k3_tarski(A_282))
      | ~ r2_hidden(D_281,D_283)
      | ~ r2_hidden(D_283,A_282) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_942,c_4])).

tff(c_1507,plain,(
    ! [A_290] :
      ( r2_hidden('#skF_14',k3_tarski(A_290))
      | ~ r2_hidden(k2_relat_1('#skF_15'),A_290) ) ),
    inference(resolution,[status(thm)],[c_896,c_1350])).

tff(c_1543,plain,(
    ! [A_9] : r2_hidden('#skF_14',k3_tarski(k2_tarski(A_9,k2_relat_1('#skF_15')))) ),
    inference(resolution,[status(thm)],[c_24,c_1507])).

tff(c_1581,plain,(
    ! [A_294] : r2_hidden('#skF_14',k2_xboole_0(A_294,k2_relat_1('#skF_15'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1543])).

tff(c_1590,plain,
    ( r2_hidden('#skF_14',k3_relat_1('#skF_15'))
    | ~ v1_relat_1('#skF_15') ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_1581])).

tff(c_1594,plain,(
    r2_hidden('#skF_14',k3_relat_1('#skF_15')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1590])).

tff(c_1596,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_798,c_1594])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:44:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.67/2.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.67/2.26  
% 4.67/2.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.67/2.26  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k1_enumset1 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_11 > #skF_6 > #skF_1 > #skF_15 > #skF_12 > #skF_4 > #skF_14 > #skF_13 > #skF_10 > #skF_2 > #skF_3 > #skF_8 > #skF_7 > #skF_9 > #skF_5
% 4.67/2.26  
% 4.67/2.26  %Foreground sorts:
% 4.67/2.26  
% 4.67/2.26  
% 4.67/2.26  %Background operators:
% 4.67/2.26  
% 4.67/2.26  
% 4.67/2.26  %Foreground operators:
% 4.67/2.26  tff('#skF_11', type, '#skF_11': ($i * $i) > $i).
% 4.67/2.26  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 4.67/2.26  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.67/2.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.67/2.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.67/2.26  tff('#skF_15', type, '#skF_15': $i).
% 4.67/2.26  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.67/2.26  tff('#skF_12', type, '#skF_12': ($i * $i * $i) > $i).
% 4.67/2.26  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 4.67/2.26  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.67/2.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.67/2.26  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.67/2.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.67/2.27  tff('#skF_14', type, '#skF_14': $i).
% 4.67/2.27  tff('#skF_13', type, '#skF_13': $i).
% 4.67/2.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.67/2.27  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 4.67/2.27  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.67/2.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.67/2.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.67/2.27  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.67/2.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.67/2.27  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.67/2.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.67/2.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.67/2.27  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 4.67/2.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.67/2.27  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 4.67/2.27  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 4.67/2.27  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.67/2.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.67/2.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.67/2.27  
% 4.67/2.29  tff(f_90, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k3_relat_1(C)) & r2_hidden(B, k3_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_relat_1)).
% 4.67/2.29  tff(f_81, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 4.67/2.29  tff(f_51, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.67/2.29  tff(f_47, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 4.67/2.29  tff(f_69, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 4.67/2.29  tff(f_53, axiom, (![A]: r1_tarski(A, k1_zfmisc_1(k3_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 4.67/2.29  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.67/2.29  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 4.67/2.29  tff(f_57, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 4.67/2.29  tff(f_61, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.67/2.29  tff(f_77, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 4.67/2.29  tff(c_78, plain, (~r2_hidden('#skF_14', k3_relat_1('#skF_15')) | ~r2_hidden('#skF_13', k3_relat_1('#skF_15'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.67/2.29  tff(c_101, plain, (~r2_hidden('#skF_13', k3_relat_1('#skF_15'))), inference(splitLeft, [status(thm)], [c_78])).
% 4.67/2.29  tff(c_82, plain, (v1_relat_1('#skF_15')), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.67/2.29  tff(c_76, plain, (![A_62]: (k2_xboole_0(k1_relat_1(A_62), k2_relat_1(A_62))=k3_relat_1(A_62) | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.67/2.29  tff(c_42, plain, (![A_17, B_18]: (k3_tarski(k2_tarski(A_17, B_18))=k2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.67/2.29  tff(c_26, plain, (![D_14, B_10]: (r2_hidden(D_14, k2_tarski(D_14, B_10)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.67/2.29  tff(c_80, plain, (r2_hidden(k4_tarski('#skF_13', '#skF_14'), '#skF_15')), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.67/2.29  tff(c_248, plain, (![C_108, A_109, D_110]: (r2_hidden(C_108, k1_relat_1(A_109)) | ~r2_hidden(k4_tarski(C_108, D_110), A_109))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.67/2.29  tff(c_267, plain, (r2_hidden('#skF_13', k1_relat_1('#skF_15'))), inference(resolution, [status(thm)], [c_80, c_248])).
% 4.67/2.29  tff(c_44, plain, (![A_19]: (r1_tarski(A_19, k1_zfmisc_1(k3_tarski(A_19))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.67/2.29  tff(c_117, plain, (![A_80, B_81]: (k3_xboole_0(A_80, B_81)=A_80 | ~r1_tarski(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.67/2.29  tff(c_121, plain, (![A_19]: (k3_xboole_0(A_19, k1_zfmisc_1(k3_tarski(A_19)))=A_19)), inference(resolution, [status(thm)], [c_44, c_117])).
% 4.67/2.29  tff(c_150, plain, (![D_88, B_89, A_90]: (r2_hidden(D_88, B_89) | ~r2_hidden(D_88, k3_xboole_0(A_90, B_89)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.67/2.29  tff(c_170, plain, (![D_96, A_97]: (r2_hidden(D_96, k1_zfmisc_1(k3_tarski(A_97))) | ~r2_hidden(D_96, A_97))), inference(superposition, [status(thm), theory('equality')], [c_121, c_150])).
% 4.67/2.29  tff(c_46, plain, (![A_20, B_21]: (m1_subset_1(A_20, B_21) | ~r2_hidden(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.67/2.29  tff(c_178, plain, (![D_98, A_99]: (m1_subset_1(D_98, k1_zfmisc_1(k3_tarski(A_99))) | ~r2_hidden(D_98, A_99))), inference(resolution, [status(thm)], [c_170, c_46])).
% 4.67/2.29  tff(c_48, plain, (![A_22, B_23]: (r1_tarski(A_22, B_23) | ~m1_subset_1(A_22, k1_zfmisc_1(B_23)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.67/2.29  tff(c_186, plain, (![D_100, A_101]: (r1_tarski(D_100, k3_tarski(A_101)) | ~r2_hidden(D_100, A_101))), inference(resolution, [status(thm)], [c_178, c_48])).
% 4.67/2.29  tff(c_20, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.67/2.29  tff(c_194, plain, (![D_102, A_103]: (k3_xboole_0(D_102, k3_tarski(A_103))=D_102 | ~r2_hidden(D_102, A_103))), inference(resolution, [status(thm)], [c_186, c_20])).
% 4.67/2.29  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.67/2.29  tff(c_669, plain, (![D_176, A_177, D_178]: (r2_hidden(D_176, k3_tarski(A_177)) | ~r2_hidden(D_176, D_178) | ~r2_hidden(D_178, A_177))), inference(superposition, [status(thm), theory('equality')], [c_194, c_4])).
% 4.67/2.29  tff(c_721, plain, (![A_179]: (r2_hidden('#skF_13', k3_tarski(A_179)) | ~r2_hidden(k1_relat_1('#skF_15'), A_179))), inference(resolution, [status(thm)], [c_267, c_669])).
% 4.67/2.29  tff(c_761, plain, (![B_10]: (r2_hidden('#skF_13', k3_tarski(k2_tarski(k1_relat_1('#skF_15'), B_10))))), inference(resolution, [status(thm)], [c_26, c_721])).
% 4.67/2.29  tff(c_782, plain, (![B_181]: (r2_hidden('#skF_13', k2_xboole_0(k1_relat_1('#skF_15'), B_181)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_761])).
% 4.67/2.29  tff(c_791, plain, (r2_hidden('#skF_13', k3_relat_1('#skF_15')) | ~v1_relat_1('#skF_15')), inference(superposition, [status(thm), theory('equality')], [c_76, c_782])).
% 4.67/2.29  tff(c_795, plain, (r2_hidden('#skF_13', k3_relat_1('#skF_15'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_791])).
% 4.67/2.29  tff(c_797, plain, $false, inference(negUnitSimplification, [status(thm)], [c_101, c_795])).
% 4.67/2.29  tff(c_798, plain, (~r2_hidden('#skF_14', k3_relat_1('#skF_15'))), inference(splitRight, [status(thm)], [c_78])).
% 4.67/2.29  tff(c_24, plain, (![D_14, A_9]: (r2_hidden(D_14, k2_tarski(A_9, D_14)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.67/2.29  tff(c_877, plain, (![C_205, A_206, D_207]: (r2_hidden(C_205, k2_relat_1(A_206)) | ~r2_hidden(k4_tarski(D_207, C_205), A_206))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.67/2.29  tff(c_896, plain, (r2_hidden('#skF_14', k2_relat_1('#skF_15'))), inference(resolution, [status(thm)], [c_80, c_877])).
% 4.67/2.29  tff(c_816, plain, (![A_184, B_185]: (k3_xboole_0(A_184, B_185)=A_184 | ~r1_tarski(A_184, B_185))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.67/2.29  tff(c_820, plain, (![A_19]: (k3_xboole_0(A_19, k1_zfmisc_1(k3_tarski(A_19)))=A_19)), inference(resolution, [status(thm)], [c_44, c_816])).
% 4.67/2.29  tff(c_848, plain, (![D_193, B_194, A_195]: (r2_hidden(D_193, B_194) | ~r2_hidden(D_193, k3_xboole_0(A_195, B_194)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.67/2.29  tff(c_861, plain, (![D_201, A_202]: (r2_hidden(D_201, k1_zfmisc_1(k3_tarski(A_202))) | ~r2_hidden(D_201, A_202))), inference(superposition, [status(thm), theory('equality')], [c_820, c_848])).
% 4.67/2.29  tff(c_869, plain, (![D_203, A_204]: (m1_subset_1(D_203, k1_zfmisc_1(k3_tarski(A_204))) | ~r2_hidden(D_203, A_204))), inference(resolution, [status(thm)], [c_861, c_46])).
% 4.67/2.29  tff(c_901, plain, (![D_208, A_209]: (r1_tarski(D_208, k3_tarski(A_209)) | ~r2_hidden(D_208, A_209))), inference(resolution, [status(thm)], [c_869, c_48])).
% 4.67/2.29  tff(c_942, plain, (![D_225, A_226]: (k3_xboole_0(D_225, k3_tarski(A_226))=D_225 | ~r2_hidden(D_225, A_226))), inference(resolution, [status(thm)], [c_901, c_20])).
% 4.67/2.29  tff(c_1350, plain, (![D_281, A_282, D_283]: (r2_hidden(D_281, k3_tarski(A_282)) | ~r2_hidden(D_281, D_283) | ~r2_hidden(D_283, A_282))), inference(superposition, [status(thm), theory('equality')], [c_942, c_4])).
% 4.67/2.29  tff(c_1507, plain, (![A_290]: (r2_hidden('#skF_14', k3_tarski(A_290)) | ~r2_hidden(k2_relat_1('#skF_15'), A_290))), inference(resolution, [status(thm)], [c_896, c_1350])).
% 4.67/2.29  tff(c_1543, plain, (![A_9]: (r2_hidden('#skF_14', k3_tarski(k2_tarski(A_9, k2_relat_1('#skF_15')))))), inference(resolution, [status(thm)], [c_24, c_1507])).
% 4.67/2.29  tff(c_1581, plain, (![A_294]: (r2_hidden('#skF_14', k2_xboole_0(A_294, k2_relat_1('#skF_15'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1543])).
% 4.67/2.29  tff(c_1590, plain, (r2_hidden('#skF_14', k3_relat_1('#skF_15')) | ~v1_relat_1('#skF_15')), inference(superposition, [status(thm), theory('equality')], [c_76, c_1581])).
% 4.67/2.29  tff(c_1594, plain, (r2_hidden('#skF_14', k3_relat_1('#skF_15'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_1590])).
% 4.67/2.29  tff(c_1596, plain, $false, inference(negUnitSimplification, [status(thm)], [c_798, c_1594])).
% 4.67/2.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.67/2.29  
% 4.67/2.29  Inference rules
% 4.67/2.29  ----------------------
% 4.67/2.29  #Ref     : 0
% 4.67/2.29  #Sup     : 344
% 4.67/2.29  #Fact    : 0
% 4.67/2.29  #Define  : 0
% 4.67/2.29  #Split   : 1
% 4.67/2.29  #Chain   : 0
% 4.67/2.29  #Close   : 0
% 4.67/2.29  
% 4.67/2.29  Ordering : KBO
% 4.67/2.29  
% 4.67/2.29  Simplification rules
% 4.67/2.29  ----------------------
% 4.67/2.29  #Subsume      : 4
% 4.67/2.29  #Demod        : 12
% 4.67/2.29  #Tautology    : 80
% 4.67/2.29  #SimpNegUnit  : 2
% 4.67/2.29  #BackRed      : 0
% 4.67/2.29  
% 4.67/2.29  #Partial instantiations: 0
% 4.67/2.29  #Strategies tried      : 1
% 4.67/2.29  
% 4.67/2.29  Timing (in seconds)
% 4.67/2.29  ----------------------
% 4.67/2.29  Preprocessing        : 0.54
% 4.67/2.29  Parsing              : 0.26
% 4.67/2.29  CNF conversion       : 0.05
% 4.67/2.29  Main loop            : 0.85
% 4.67/2.29  Inferencing          : 0.31
% 4.67/2.29  Reduction            : 0.26
% 4.67/2.29  Demodulation         : 0.19
% 4.67/2.29  BG Simplification    : 0.05
% 4.67/2.30  Subsumption          : 0.15
% 4.67/2.30  Abstraction          : 0.05
% 4.67/2.30  MUC search           : 0.00
% 4.67/2.30  Cooper               : 0.00
% 4.67/2.30  Total                : 1.45
% 4.67/2.30  Index Insertion      : 0.00
% 4.67/2.30  Index Deletion       : 0.00
% 4.67/2.30  Index Matching       : 0.00
% 4.67/2.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
