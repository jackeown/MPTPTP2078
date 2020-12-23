%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0497+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:24 EST 2020

% Result     : Theorem 53.81s
% Output     : CNFRefutation 53.88s
% Verified   : 
% Statistics : Number of formulae       :  119 (1089 expanded)
%              Number of leaves         :   38 ( 391 expanded)
%              Depth                    :   21
%              Number of atoms          :  227 (2208 expanded)
%              Number of equality atoms :   49 ( 350 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_relat_1 > k4_tarski > k3_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_4 > #skF_13 > #skF_2 > #skF_9 > #skF_11 > #skF_3 > #skF_8 > #skF_7 > #skF_5 > #skF_12 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_11',type,(
    '#skF_11': $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_30,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_97,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k7_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_69,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_68,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_52,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_28,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( v1_relat_1(C)
         => ( C = k7_relat_1(A,B)
          <=> ! [D,E] :
                ( r2_hidden(k4_tarski(D,E),C)
              <=> ( r2_hidden(D,B)
                  & r2_hidden(k4_tarski(D,E),A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_4,plain,(
    ! [B_3,A_2] : k3_xboole_0(B_3,A_2) = k3_xboole_0(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_217043,plain,(
    ! [A_2188,B_2189] :
      ( r1_xboole_0(A_2188,B_2189)
      | k3_xboole_0(A_2188,B_2189) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_74,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_13'),'#skF_12')
    | k7_relat_1('#skF_13','#skF_12') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_102,plain,(
    k7_relat_1('#skF_13','#skF_12') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_72,plain,(
    v1_relat_1('#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_60,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_58,plain,(
    ! [A_50] : m1_subset_1('#skF_11'(A_50),A_50) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_66,plain,(
    ! [A_55,B_56] :
      ( r2_hidden(A_55,B_56)
      | v1_xboole_0(B_56)
      | ~ m1_subset_1(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_404,plain,(
    ! [C_102,A_103] :
      ( r2_hidden(k4_tarski(C_102,'#skF_8'(A_103,k1_relat_1(A_103),C_102)),A_103)
      | ~ r2_hidden(C_102,k1_relat_1(A_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_70,plain,(
    ! [B_59,A_58] :
      ( ~ v1_xboole_0(B_59)
      | ~ r2_hidden(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_436,plain,(
    ! [A_104,C_105] :
      ( ~ v1_xboole_0(A_104)
      | ~ r2_hidden(C_105,k1_relat_1(A_104)) ) ),
    inference(resolution,[status(thm)],[c_404,c_70])).

tff(c_42364,plain,(
    ! [A_807,A_808] :
      ( ~ v1_xboole_0(A_807)
      | v1_xboole_0(k1_relat_1(A_807))
      | ~ m1_subset_1(A_808,k1_relat_1(A_807)) ) ),
    inference(resolution,[status(thm)],[c_66,c_436])).

tff(c_42369,plain,(
    ! [A_809] :
      ( ~ v1_xboole_0(A_809)
      | v1_xboole_0(k1_relat_1(A_809)) ) ),
    inference(resolution,[status(thm)],[c_58,c_42364])).

tff(c_68,plain,(
    ! [A_57] :
      ( k1_xboole_0 = A_57
      | ~ v1_xboole_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_42426,plain,(
    ! [A_813] :
      ( k1_relat_1(A_813) = k1_xboole_0
      | ~ v1_xboole_0(A_813) ) ),
    inference(resolution,[status(thm)],[c_42369,c_68])).

tff(c_42434,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_60,c_42426])).

tff(c_24,plain,(
    ! [C_38,A_23] :
      ( r2_hidden(k4_tarski(C_38,'#skF_8'(A_23,k1_relat_1(A_23),C_38)),A_23)
      | ~ r2_hidden(C_38,k1_relat_1(A_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_447,plain,(
    ! [A_106,C_107] :
      ( ~ v1_xboole_0(A_106)
      | ~ r2_hidden(C_107,k1_relat_1(k1_relat_1(A_106))) ) ),
    inference(resolution,[status(thm)],[c_24,c_436])).

tff(c_456,plain,(
    ! [A_106,C_38] :
      ( ~ v1_xboole_0(A_106)
      | ~ r2_hidden(C_38,k1_relat_1(k1_relat_1(k1_relat_1(A_106)))) ) ),
    inference(resolution,[status(thm)],[c_24,c_447])).

tff(c_42444,plain,(
    ! [C_38] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(C_38,k1_relat_1(k1_relat_1(k1_xboole_0))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42434,c_456])).

tff(c_42461,plain,(
    ! [C_38] : ~ r2_hidden(C_38,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42434,c_42434,c_60,c_42444])).

tff(c_87,plain,(
    ! [A_61] :
      ( v1_relat_1(A_61)
      | ~ v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_91,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_60,c_87])).

tff(c_48400,plain,(
    ! [A_955,B_956,C_957] :
      ( r2_hidden('#skF_1'(A_955,B_956,C_957),B_956)
      | r2_hidden(k4_tarski('#skF_3'(A_955,B_956,C_957),'#skF_4'(A_955,B_956,C_957)),C_957)
      | k7_relat_1(A_955,B_956) = C_957
      | ~ v1_relat_1(C_957)
      | ~ v1_relat_1(A_955) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_57595,plain,(
    ! [C_1124,A_1125,B_1126] :
      ( ~ v1_xboole_0(C_1124)
      | r2_hidden('#skF_1'(A_1125,B_1126,C_1124),B_1126)
      | k7_relat_1(A_1125,B_1126) = C_1124
      | ~ v1_relat_1(C_1124)
      | ~ v1_relat_1(A_1125) ) ),
    inference(resolution,[status(thm)],[c_48400,c_70])).

tff(c_148409,plain,(
    ! [C_1772,A_1773] :
      ( ~ v1_xboole_0(C_1772)
      | k7_relat_1(A_1773,k1_xboole_0) = C_1772
      | ~ v1_relat_1(C_1772)
      | ~ v1_relat_1(A_1773) ) ),
    inference(resolution,[status(thm)],[c_57595,c_42461])).

tff(c_148489,plain,(
    ! [A_1773] :
      ( k7_relat_1(A_1773,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_1773) ) ),
    inference(resolution,[status(thm)],[c_60,c_148409])).

tff(c_148532,plain,(
    ! [A_1774] :
      ( k7_relat_1(A_1774,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_1774) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_148489])).

tff(c_148697,plain,(
    k7_relat_1('#skF_13',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_72,c_148532])).

tff(c_22,plain,(
    ! [D_21,B_15,E_22,A_4] :
      ( r2_hidden(D_21,B_15)
      | ~ r2_hidden(k4_tarski(D_21,E_22),k7_relat_1(A_4,B_15))
      | ~ v1_relat_1(k7_relat_1(A_4,B_15))
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_48457,plain,(
    ! [A_955,B_956,A_4,B_15] :
      ( r2_hidden('#skF_3'(A_955,B_956,k7_relat_1(A_4,B_15)),B_15)
      | ~ v1_relat_1(A_4)
      | r2_hidden('#skF_1'(A_955,B_956,k7_relat_1(A_4,B_15)),B_956)
      | k7_relat_1(A_955,B_956) = k7_relat_1(A_4,B_15)
      | ~ v1_relat_1(k7_relat_1(A_4,B_15))
      | ~ v1_relat_1(A_955) ) ),
    inference(resolution,[status(thm)],[c_48400,c_22])).

tff(c_148726,plain,(
    ! [A_955,B_956] :
      ( r2_hidden('#skF_3'(A_955,B_956,k7_relat_1('#skF_13',k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1('#skF_13')
      | r2_hidden('#skF_1'(A_955,B_956,k1_xboole_0),B_956)
      | k7_relat_1(A_955,B_956) = k7_relat_1('#skF_13',k1_xboole_0)
      | ~ v1_relat_1(k7_relat_1('#skF_13',k1_xboole_0))
      | ~ v1_relat_1(A_955) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148697,c_48457])).

tff(c_148780,plain,(
    ! [A_955,B_956] :
      ( r2_hidden('#skF_3'(A_955,B_956,k1_xboole_0),k1_xboole_0)
      | r2_hidden('#skF_1'(A_955,B_956,k1_xboole_0),B_956)
      | k7_relat_1(A_955,B_956) = k1_xboole_0
      | ~ v1_relat_1(A_955) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_148697,c_148697,c_72,c_148697,c_148726])).

tff(c_148781,plain,(
    ! [A_955,B_956] :
      ( r2_hidden('#skF_1'(A_955,B_956,k1_xboole_0),B_956)
      | k7_relat_1(A_955,B_956) = k1_xboole_0
      | ~ v1_relat_1(A_955) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42461,c_148780])).

tff(c_49087,plain,(
    ! [A_965,B_966,C_967] :
      ( r2_hidden(k4_tarski('#skF_1'(A_965,B_966,C_967),'#skF_2'(A_965,B_966,C_967)),A_965)
      | r2_hidden(k4_tarski('#skF_3'(A_965,B_966,C_967),'#skF_4'(A_965,B_966,C_967)),C_967)
      | k7_relat_1(A_965,B_966) = C_967
      | ~ v1_relat_1(C_967)
      | ~ v1_relat_1(A_965) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_49212,plain,(
    ! [A_965,B_966,A_4,B_15] :
      ( r2_hidden('#skF_3'(A_965,B_966,k7_relat_1(A_4,B_15)),B_15)
      | ~ v1_relat_1(A_4)
      | r2_hidden(k4_tarski('#skF_1'(A_965,B_966,k7_relat_1(A_4,B_15)),'#skF_2'(A_965,B_966,k7_relat_1(A_4,B_15))),A_965)
      | k7_relat_1(A_965,B_966) = k7_relat_1(A_4,B_15)
      | ~ v1_relat_1(k7_relat_1(A_4,B_15))
      | ~ v1_relat_1(A_965) ) ),
    inference(resolution,[status(thm)],[c_49087,c_22])).

tff(c_148701,plain,(
    ! [A_965,B_966] :
      ( r2_hidden('#skF_3'(A_965,B_966,k7_relat_1('#skF_13',k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1('#skF_13')
      | r2_hidden(k4_tarski('#skF_1'(A_965,B_966,k1_xboole_0),'#skF_2'(A_965,B_966,k7_relat_1('#skF_13',k1_xboole_0))),A_965)
      | k7_relat_1(A_965,B_966) = k7_relat_1('#skF_13',k1_xboole_0)
      | ~ v1_relat_1(k7_relat_1('#skF_13',k1_xboole_0))
      | ~ v1_relat_1(A_965) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148697,c_49212])).

tff(c_148760,plain,(
    ! [A_965,B_966] :
      ( r2_hidden('#skF_3'(A_965,B_966,k1_xboole_0),k1_xboole_0)
      | r2_hidden(k4_tarski('#skF_1'(A_965,B_966,k1_xboole_0),'#skF_2'(A_965,B_966,k1_xboole_0)),A_965)
      | k7_relat_1(A_965,B_966) = k1_xboole_0
      | ~ v1_relat_1(A_965) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_148697,c_148697,c_148697,c_72,c_148697,c_148701])).

tff(c_160575,plain,(
    ! [A_1837,B_1838] :
      ( r2_hidden(k4_tarski('#skF_1'(A_1837,B_1838,k1_xboole_0),'#skF_2'(A_1837,B_1838,k1_xboole_0)),A_1837)
      | k7_relat_1(A_1837,B_1838) = k1_xboole_0
      | ~ v1_relat_1(A_1837) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42461,c_148760])).

tff(c_26,plain,(
    ! [C_38,A_23,D_41] :
      ( r2_hidden(C_38,k1_relat_1(A_23))
      | ~ r2_hidden(k4_tarski(C_38,D_41),A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_216454,plain,(
    ! [A_2181,B_2182] :
      ( r2_hidden('#skF_1'(A_2181,B_2182,k1_xboole_0),k1_relat_1(A_2181))
      | k7_relat_1(A_2181,B_2182) = k1_xboole_0
      | ~ v1_relat_1(A_2181) ) ),
    inference(resolution,[status(thm)],[c_160575,c_26])).

tff(c_80,plain,
    ( k7_relat_1('#skF_13','#skF_12') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_13'),'#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_203,plain,(
    r1_xboole_0(k1_relat_1('#skF_13'),'#skF_12') ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_80])).

tff(c_54,plain,(
    ! [A_48,B_49] :
      ( k3_xboole_0(A_48,B_49) = k1_xboole_0
      | ~ r1_xboole_0(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_209,plain,(
    k3_xboole_0(k1_relat_1('#skF_13'),'#skF_12') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_203,c_54])).

tff(c_329,plain,(
    ! [D_92,A_93,B_94] :
      ( r2_hidden(D_92,k3_xboole_0(A_93,B_94))
      | ~ r2_hidden(D_92,B_94)
      | ~ r2_hidden(D_92,A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_365,plain,(
    ! [A_95,B_96,D_97] :
      ( ~ v1_xboole_0(k3_xboole_0(A_95,B_96))
      | ~ r2_hidden(D_97,B_96)
      | ~ r2_hidden(D_97,A_95) ) ),
    inference(resolution,[status(thm)],[c_329,c_70])).

tff(c_369,plain,(
    ! [D_97] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(D_97,'#skF_12')
      | ~ r2_hidden(D_97,k1_relat_1('#skF_13')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_365])).

tff(c_381,plain,(
    ! [D_97] :
      ( ~ r2_hidden(D_97,'#skF_12')
      | ~ r2_hidden(D_97,k1_relat_1('#skF_13')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_369])).

tff(c_216565,plain,(
    ! [B_2182] :
      ( ~ r2_hidden('#skF_1'('#skF_13',B_2182,k1_xboole_0),'#skF_12')
      | k7_relat_1('#skF_13',B_2182) = k1_xboole_0
      | ~ v1_relat_1('#skF_13') ) ),
    inference(resolution,[status(thm)],[c_216454,c_381])).

tff(c_216971,plain,(
    ! [B_2185] :
      ( ~ r2_hidden('#skF_1'('#skF_13',B_2185,k1_xboole_0),'#skF_12')
      | k7_relat_1('#skF_13',B_2185) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_216565])).

tff(c_216975,plain,
    ( k7_relat_1('#skF_13','#skF_12') = k1_xboole_0
    | ~ v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_148781,c_216971])).

tff(c_216987,plain,(
    k7_relat_1('#skF_13','#skF_12') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_216975])).

tff(c_216989,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_216987])).

tff(c_216990,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_13'),'#skF_12') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_217046,plain,(
    k3_xboole_0(k1_relat_1('#skF_13'),'#skF_12') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_217043,c_216990])).

tff(c_217050,plain,(
    k3_xboole_0('#skF_12',k1_relat_1('#skF_13')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_217046])).

tff(c_218013,plain,(
    ! [A_2264,B_2265,C_2266] :
      ( r2_hidden('#skF_9'(A_2264,B_2265,C_2266),A_2264)
      | r2_hidden('#skF_10'(A_2264,B_2265,C_2266),C_2266)
      | k3_xboole_0(A_2264,B_2265) = C_2266 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_225454,plain,(
    ! [C_2462,A_2463,B_2464] :
      ( ~ v1_xboole_0(C_2462)
      | r2_hidden('#skF_9'(A_2463,B_2464,C_2462),A_2463)
      | k3_xboole_0(A_2463,B_2464) = C_2462 ) ),
    inference(resolution,[status(thm)],[c_218013,c_70])).

tff(c_217529,plain,(
    ! [A_2247,B_2248,C_2249] :
      ( r2_hidden('#skF_9'(A_2247,B_2248,C_2249),B_2248)
      | r2_hidden('#skF_10'(A_2247,B_2248,C_2249),C_2249)
      | k3_xboole_0(A_2247,B_2248) = C_2249 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_223852,plain,(
    ! [C_2417,A_2418,B_2419] :
      ( ~ v1_xboole_0(C_2417)
      | r2_hidden('#skF_9'(A_2418,B_2419,C_2417),B_2419)
      | k3_xboole_0(A_2418,B_2419) = C_2417 ) ),
    inference(resolution,[status(thm)],[c_217529,c_70])).

tff(c_217265,plain,(
    ! [C_2224,A_2225] :
      ( r2_hidden(k4_tarski(C_2224,'#skF_8'(A_2225,k1_relat_1(A_2225),C_2224)),A_2225)
      | ~ r2_hidden(C_2224,k1_relat_1(A_2225)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_217296,plain,(
    ! [A_2226,C_2227] :
      ( ~ v1_xboole_0(A_2226)
      | ~ r2_hidden(C_2227,k1_relat_1(A_2226)) ) ),
    inference(resolution,[status(thm)],[c_217265,c_70])).

tff(c_217344,plain,(
    ! [A_2232,A_2233] :
      ( ~ v1_xboole_0(A_2232)
      | v1_xboole_0(k1_relat_1(A_2232))
      | ~ m1_subset_1(A_2233,k1_relat_1(A_2232)) ) ),
    inference(resolution,[status(thm)],[c_66,c_217296])).

tff(c_217349,plain,(
    ! [A_2234] :
      ( ~ v1_xboole_0(A_2234)
      | v1_xboole_0(k1_relat_1(A_2234)) ) ),
    inference(resolution,[status(thm)],[c_58,c_217344])).

tff(c_217368,plain,(
    ! [A_2239] :
      ( k1_relat_1(A_2239) = k1_xboole_0
      | ~ v1_xboole_0(A_2239) ) ),
    inference(resolution,[status(thm)],[c_217349,c_68])).

tff(c_217376,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_60,c_217368])).

tff(c_217312,plain,(
    ! [A_2228,C_2229] :
      ( ~ v1_xboole_0(A_2228)
      | ~ r2_hidden(C_2229,k1_relat_1(k1_relat_1(A_2228))) ) ),
    inference(resolution,[status(thm)],[c_24,c_217296])).

tff(c_217325,plain,(
    ! [A_2228,C_38] :
      ( ~ v1_xboole_0(A_2228)
      | ~ r2_hidden(C_38,k1_relat_1(k1_relat_1(k1_relat_1(A_2228)))) ) ),
    inference(resolution,[status(thm)],[c_24,c_217312])).

tff(c_217386,plain,(
    ! [C_38] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(C_38,k1_relat_1(k1_relat_1(k1_xboole_0))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_217376,c_217325])).

tff(c_217403,plain,(
    ! [C_38] : ~ r2_hidden(C_38,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_217376,c_217376,c_60,c_217386])).

tff(c_216991,plain,(
    k7_relat_1('#skF_13','#skF_12') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_218604,plain,(
    ! [D_2297,E_2298,A_2299,B_2300] :
      ( r2_hidden(k4_tarski(D_2297,E_2298),k7_relat_1(A_2299,B_2300))
      | ~ r2_hidden(k4_tarski(D_2297,E_2298),A_2299)
      | ~ r2_hidden(D_2297,B_2300)
      | ~ v1_relat_1(k7_relat_1(A_2299,B_2300))
      | ~ v1_relat_1(A_2299) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_218622,plain,(
    ! [D_2297,E_2298] :
      ( r2_hidden(k4_tarski(D_2297,E_2298),k1_xboole_0)
      | ~ r2_hidden(k4_tarski(D_2297,E_2298),'#skF_13')
      | ~ r2_hidden(D_2297,'#skF_12')
      | ~ v1_relat_1(k7_relat_1('#skF_13','#skF_12'))
      | ~ v1_relat_1('#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_216991,c_218604])).

tff(c_218629,plain,(
    ! [D_2297,E_2298] :
      ( r2_hidden(k4_tarski(D_2297,E_2298),k1_xboole_0)
      | ~ r2_hidden(k4_tarski(D_2297,E_2298),'#skF_13')
      | ~ r2_hidden(D_2297,'#skF_12') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_91,c_216991,c_218622])).

tff(c_218631,plain,(
    ! [D_2301,E_2302] :
      ( ~ r2_hidden(k4_tarski(D_2301,E_2302),'#skF_13')
      | ~ r2_hidden(D_2301,'#skF_12') ) ),
    inference(negUnitSimplification,[status(thm)],[c_217403,c_218629])).

tff(c_218644,plain,(
    ! [C_38] :
      ( ~ r2_hidden(C_38,'#skF_12')
      | ~ r2_hidden(C_38,k1_relat_1('#skF_13')) ) ),
    inference(resolution,[status(thm)],[c_24,c_218631])).

tff(c_223906,plain,(
    ! [A_2418,C_2417] :
      ( ~ r2_hidden('#skF_9'(A_2418,k1_relat_1('#skF_13'),C_2417),'#skF_12')
      | ~ v1_xboole_0(C_2417)
      | k3_xboole_0(A_2418,k1_relat_1('#skF_13')) = C_2417 ) ),
    inference(resolution,[status(thm)],[c_223852,c_218644])).

tff(c_225524,plain,(
    ! [C_2465] :
      ( ~ v1_xboole_0(C_2465)
      | k3_xboole_0('#skF_12',k1_relat_1('#skF_13')) = C_2465 ) ),
    inference(resolution,[status(thm)],[c_225454,c_223906])).

tff(c_225540,plain,(
    k3_xboole_0('#skF_12',k1_relat_1('#skF_13')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_60,c_225524])).

tff(c_225551,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_217050,c_225540])).

%------------------------------------------------------------------------------
