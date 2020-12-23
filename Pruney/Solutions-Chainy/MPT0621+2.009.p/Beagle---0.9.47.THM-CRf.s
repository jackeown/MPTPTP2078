%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:00 EST 2020

% Result     : Theorem 6.28s
% Output     : CNFRefutation 6.28s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 209 expanded)
%              Number of leaves         :   28 (  85 expanded)
%              Depth                    :   16
%              Number of atoms          :  130 ( 468 expanded)
%              Number of equality atoms :   59 ( 145 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k4_tarski > k3_xboole_0 > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_4 > #skF_2 > #skF_8 > #skF_5 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_99,negated_conjecture,(
    ~ ! [A] :
        ( ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ! [C] :
                ( ( v1_relat_1(C)
                  & v1_funct_1(C) )
               => ( ( k1_relat_1(B) = A
                    & k1_relat_1(C) = A )
                 => B = C ) ) )
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_1)).

tff(f_80,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(f_68,axiom,(
    ! [A,B] :
    ? [C] :
      ( v1_relat_1(C)
      & v1_funct_1(C)
      & k1_relat_1(C) = A
      & ! [D] :
          ( r2_hidden(D,A)
         => k1_funct_1(C,D) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(E,D),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).

tff(f_43,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_42,plain,(
    ! [A_57] : v1_relat_1('#skF_7'(A_57)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_34,plain,(
    ! [A_50,B_51] : v1_relat_1('#skF_6'(A_50,B_51)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_393,plain,(
    ! [A_141,B_142,C_143] :
      ( r2_hidden('#skF_3'(A_141,B_142,C_143),B_142)
      | r2_hidden('#skF_4'(A_141,B_142,C_143),C_143)
      | k9_relat_1(A_141,B_142) = C_143
      | ~ v1_relat_1(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8,plain,(
    ! [A_7] : r1_xboole_0(A_7,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_97,plain,(
    ! [A_84,B_85,C_86] :
      ( ~ r1_xboole_0(A_84,B_85)
      | ~ r2_hidden(C_86,k3_xboole_0(A_84,B_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_100,plain,(
    ! [A_6,C_86] :
      ( ~ r1_xboole_0(A_6,k1_xboole_0)
      | ~ r2_hidden(C_86,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_97])).

tff(c_102,plain,(
    ! [C_86] : ~ r2_hidden(C_86,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_100])).

tff(c_459,plain,(
    ! [A_144,B_145] :
      ( r2_hidden('#skF_3'(A_144,B_145,k1_xboole_0),B_145)
      | k9_relat_1(A_144,B_145) = k1_xboole_0
      | ~ v1_relat_1(A_144) ) ),
    inference(resolution,[status(thm)],[c_393,c_102])).

tff(c_494,plain,(
    ! [A_146] :
      ( k9_relat_1(A_146,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_146) ) ),
    inference(resolution,[status(thm)],[c_459,c_102])).

tff(c_501,plain,(
    ! [A_50,B_51] : k9_relat_1('#skF_6'(A_50,B_51),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_494])).

tff(c_329,plain,(
    ! [A_116,B_117,D_118] :
      ( r2_hidden('#skF_5'(A_116,B_117,k9_relat_1(A_116,B_117),D_118),B_117)
      | ~ r2_hidden(D_118,k9_relat_1(A_116,B_117))
      | ~ v1_relat_1(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_344,plain,(
    ! [D_118,A_116] :
      ( ~ r2_hidden(D_118,k9_relat_1(A_116,k1_xboole_0))
      | ~ v1_relat_1(A_116) ) ),
    inference(resolution,[status(thm)],[c_329,c_102])).

tff(c_3208,plain,(
    ! [A_3032,A_3033,C_3034] :
      ( ~ v1_relat_1(A_3032)
      | r2_hidden('#skF_4'(A_3033,k9_relat_1(A_3032,k1_xboole_0),C_3034),C_3034)
      | k9_relat_1(A_3033,k9_relat_1(A_3032,k1_xboole_0)) = C_3034
      | ~ v1_relat_1(A_3033) ) ),
    inference(resolution,[status(thm)],[c_393,c_344])).

tff(c_3277,plain,(
    ! [A_50,B_51,A_3033,C_3034] :
      ( ~ v1_relat_1('#skF_6'(A_50,B_51))
      | r2_hidden('#skF_4'(A_3033,k1_xboole_0,C_3034),C_3034)
      | k9_relat_1(A_3033,k9_relat_1('#skF_6'(A_50,B_51),k1_xboole_0)) = C_3034
      | ~ v1_relat_1(A_3033) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_501,c_3208])).

tff(c_3302,plain,(
    ! [A_3033,C_3034] :
      ( r2_hidden('#skF_4'(A_3033,k1_xboole_0,C_3034),C_3034)
      | k9_relat_1(A_3033,k1_xboole_0) = C_3034
      | ~ v1_relat_1(A_3033) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_501,c_34,c_3277])).

tff(c_3305,plain,(
    ! [A_3035,C_3036] :
      ( r2_hidden('#skF_4'(A_3035,k1_xboole_0,C_3036),C_3036)
      | k9_relat_1(A_3035,k1_xboole_0) = C_3036
      | ~ v1_relat_1(A_3035) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_501,c_34,c_3277])).

tff(c_32,plain,(
    ! [A_50,B_51] : v1_funct_1('#skF_6'(A_50,B_51)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_30,plain,(
    ! [A_50,B_51] : k1_relat_1('#skF_6'(A_50,B_51)) = A_50 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_40,plain,(
    ! [A_57] : v1_funct_1('#skF_7'(A_57)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_38,plain,(
    ! [A_57] : k1_relat_1('#skF_7'(A_57)) = A_57 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_77,plain,(
    ! [C_80,B_81] :
      ( C_80 = B_81
      | k1_relat_1(C_80) != '#skF_8'
      | k1_relat_1(B_81) != '#skF_8'
      | ~ v1_funct_1(C_80)
      | ~ v1_relat_1(C_80)
      | ~ v1_funct_1(B_81)
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_81,plain,(
    ! [B_81,A_57] :
      ( B_81 = '#skF_7'(A_57)
      | k1_relat_1('#skF_7'(A_57)) != '#skF_8'
      | k1_relat_1(B_81) != '#skF_8'
      | ~ v1_funct_1('#skF_7'(A_57))
      | ~ v1_funct_1(B_81)
      | ~ v1_relat_1(B_81) ) ),
    inference(resolution,[status(thm)],[c_42,c_77])).

tff(c_128,plain,(
    ! [B_97,A_98] :
      ( B_97 = '#skF_7'(A_98)
      | A_98 != '#skF_8'
      | k1_relat_1(B_97) != '#skF_8'
      | ~ v1_funct_1(B_97)
      | ~ v1_relat_1(B_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_81])).

tff(c_130,plain,(
    ! [A_98,A_50,B_51] :
      ( '#skF_7'(A_98) = '#skF_6'(A_50,B_51)
      | A_98 != '#skF_8'
      | k1_relat_1('#skF_6'(A_50,B_51)) != '#skF_8'
      | ~ v1_funct_1('#skF_6'(A_50,B_51)) ) ),
    inference(resolution,[status(thm)],[c_34,c_128])).

tff(c_209,plain,(
    ! [A_106,A_107,B_108] :
      ( '#skF_7'(A_106) = '#skF_6'(A_107,B_108)
      | A_106 != '#skF_8'
      | A_107 != '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_130])).

tff(c_28,plain,(
    ! [A_50,B_51,D_56] :
      ( k1_funct_1('#skF_6'(A_50,B_51),D_56) = B_51
      | ~ r2_hidden(D_56,A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_224,plain,(
    ! [A_106,D_56,B_108,A_107] :
      ( k1_funct_1('#skF_7'(A_106),D_56) = B_108
      | ~ r2_hidden(D_56,A_107)
      | A_106 != '#skF_8'
      | A_107 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_28])).

tff(c_5003,plain,(
    ! [A_3145,A_3146,C_3147] :
      ( k1_funct_1('#skF_7'(A_3145),'#skF_4'(A_3146,k1_xboole_0,C_3147)) = '#skF_8'
      | A_3145 != '#skF_8'
      | C_3147 != '#skF_8'
      | k9_relat_1(A_3146,k1_xboole_0) = C_3147
      | ~ v1_relat_1(A_3146) ) ),
    inference(resolution,[status(thm)],[c_3305,c_224])).

tff(c_36,plain,(
    ! [A_57,C_62] :
      ( k1_funct_1('#skF_7'(A_57),C_62) = k1_xboole_0
      | ~ r2_hidden(C_62,A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_5006,plain,(
    ! [A_3146,C_3147,A_3145] :
      ( k1_xboole_0 = '#skF_8'
      | ~ r2_hidden('#skF_4'(A_3146,k1_xboole_0,C_3147),A_3145)
      | A_3145 != '#skF_8'
      | C_3147 != '#skF_8'
      | k9_relat_1(A_3146,k1_xboole_0) = C_3147
      | ~ v1_relat_1(A_3146) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5003,c_36])).

tff(c_5133,plain,(
    ! [A_5741,C_5742,A_5743] :
      ( ~ r2_hidden('#skF_4'(A_5741,k1_xboole_0,C_5742),A_5743)
      | A_5743 != '#skF_8'
      | C_5742 != '#skF_8'
      | k9_relat_1(A_5741,k1_xboole_0) = C_5742
      | ~ v1_relat_1(A_5741) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_5006])).

tff(c_5152,plain,(
    ! [C_3034,A_3033] :
      ( C_3034 != '#skF_8'
      | k9_relat_1(A_3033,k1_xboole_0) = C_3034
      | ~ v1_relat_1(A_3033) ) ),
    inference(resolution,[status(thm)],[c_3302,c_5133])).

tff(c_5223,plain,(
    ! [A_5805] :
      ( k9_relat_1(A_5805,k1_xboole_0) = '#skF_8'
      | ~ v1_relat_1(A_5805) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_5152])).

tff(c_5231,plain,(
    ! [A_57] : k9_relat_1('#skF_7'(A_57),k1_xboole_0) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_42,c_5223])).

tff(c_502,plain,(
    ! [A_57] : k9_relat_1('#skF_7'(A_57),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_494])).

tff(c_5232,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5231,c_502])).

tff(c_5234,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_5232])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:43:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.28/2.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.28/2.32  
% 6.28/2.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.28/2.33  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k4_tarski > k3_xboole_0 > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_4 > #skF_2 > #skF_8 > #skF_5 > #skF_3 > #skF_1
% 6.28/2.33  
% 6.28/2.33  %Foreground sorts:
% 6.28/2.33  
% 6.28/2.33  
% 6.28/2.33  %Background operators:
% 6.28/2.33  
% 6.28/2.33  
% 6.28/2.33  %Foreground operators:
% 6.28/2.33  tff('#skF_7', type, '#skF_7': $i > $i).
% 6.28/2.33  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 6.28/2.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.28/2.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.28/2.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.28/2.33  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.28/2.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.28/2.33  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 6.28/2.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.28/2.33  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.28/2.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.28/2.33  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.28/2.33  tff('#skF_8', type, '#skF_8': $i).
% 6.28/2.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.28/2.33  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 6.28/2.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.28/2.33  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.28/2.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.28/2.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.28/2.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.28/2.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.28/2.33  
% 6.28/2.34  tff(f_99, negated_conjecture, ~(![A]: ((![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) => (B = C)))))) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_1)).
% 6.28/2.34  tff(f_80, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 6.28/2.34  tff(f_68, axiom, (![A, B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (![D]: (r2_hidden(D, A) => (k1_funct_1(C, D) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 6.28/2.34  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(E, D), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_relat_1)).
% 6.28/2.34  tff(f_43, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 6.28/2.34  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 6.28/2.34  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 6.28/2.34  tff(c_44, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.28/2.34  tff(c_42, plain, (![A_57]: (v1_relat_1('#skF_7'(A_57)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.28/2.34  tff(c_34, plain, (![A_50, B_51]: (v1_relat_1('#skF_6'(A_50, B_51)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.28/2.34  tff(c_393, plain, (![A_141, B_142, C_143]: (r2_hidden('#skF_3'(A_141, B_142, C_143), B_142) | r2_hidden('#skF_4'(A_141, B_142, C_143), C_143) | k9_relat_1(A_141, B_142)=C_143 | ~v1_relat_1(A_141))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.28/2.34  tff(c_8, plain, (![A_7]: (r1_xboole_0(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.28/2.34  tff(c_6, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.28/2.34  tff(c_97, plain, (![A_84, B_85, C_86]: (~r1_xboole_0(A_84, B_85) | ~r2_hidden(C_86, k3_xboole_0(A_84, B_85)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.28/2.34  tff(c_100, plain, (![A_6, C_86]: (~r1_xboole_0(A_6, k1_xboole_0) | ~r2_hidden(C_86, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_97])).
% 6.28/2.34  tff(c_102, plain, (![C_86]: (~r2_hidden(C_86, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_100])).
% 6.28/2.34  tff(c_459, plain, (![A_144, B_145]: (r2_hidden('#skF_3'(A_144, B_145, k1_xboole_0), B_145) | k9_relat_1(A_144, B_145)=k1_xboole_0 | ~v1_relat_1(A_144))), inference(resolution, [status(thm)], [c_393, c_102])).
% 6.28/2.34  tff(c_494, plain, (![A_146]: (k9_relat_1(A_146, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_146))), inference(resolution, [status(thm)], [c_459, c_102])).
% 6.28/2.34  tff(c_501, plain, (![A_50, B_51]: (k9_relat_1('#skF_6'(A_50, B_51), k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_494])).
% 6.28/2.34  tff(c_329, plain, (![A_116, B_117, D_118]: (r2_hidden('#skF_5'(A_116, B_117, k9_relat_1(A_116, B_117), D_118), B_117) | ~r2_hidden(D_118, k9_relat_1(A_116, B_117)) | ~v1_relat_1(A_116))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.28/2.34  tff(c_344, plain, (![D_118, A_116]: (~r2_hidden(D_118, k9_relat_1(A_116, k1_xboole_0)) | ~v1_relat_1(A_116))), inference(resolution, [status(thm)], [c_329, c_102])).
% 6.28/2.34  tff(c_3208, plain, (![A_3032, A_3033, C_3034]: (~v1_relat_1(A_3032) | r2_hidden('#skF_4'(A_3033, k9_relat_1(A_3032, k1_xboole_0), C_3034), C_3034) | k9_relat_1(A_3033, k9_relat_1(A_3032, k1_xboole_0))=C_3034 | ~v1_relat_1(A_3033))), inference(resolution, [status(thm)], [c_393, c_344])).
% 6.28/2.34  tff(c_3277, plain, (![A_50, B_51, A_3033, C_3034]: (~v1_relat_1('#skF_6'(A_50, B_51)) | r2_hidden('#skF_4'(A_3033, k1_xboole_0, C_3034), C_3034) | k9_relat_1(A_3033, k9_relat_1('#skF_6'(A_50, B_51), k1_xboole_0))=C_3034 | ~v1_relat_1(A_3033))), inference(superposition, [status(thm), theory('equality')], [c_501, c_3208])).
% 6.28/2.34  tff(c_3302, plain, (![A_3033, C_3034]: (r2_hidden('#skF_4'(A_3033, k1_xboole_0, C_3034), C_3034) | k9_relat_1(A_3033, k1_xboole_0)=C_3034 | ~v1_relat_1(A_3033))), inference(demodulation, [status(thm), theory('equality')], [c_501, c_34, c_3277])).
% 6.28/2.34  tff(c_3305, plain, (![A_3035, C_3036]: (r2_hidden('#skF_4'(A_3035, k1_xboole_0, C_3036), C_3036) | k9_relat_1(A_3035, k1_xboole_0)=C_3036 | ~v1_relat_1(A_3035))), inference(demodulation, [status(thm), theory('equality')], [c_501, c_34, c_3277])).
% 6.28/2.34  tff(c_32, plain, (![A_50, B_51]: (v1_funct_1('#skF_6'(A_50, B_51)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.28/2.34  tff(c_30, plain, (![A_50, B_51]: (k1_relat_1('#skF_6'(A_50, B_51))=A_50)), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.28/2.34  tff(c_40, plain, (![A_57]: (v1_funct_1('#skF_7'(A_57)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.28/2.34  tff(c_38, plain, (![A_57]: (k1_relat_1('#skF_7'(A_57))=A_57)), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.28/2.34  tff(c_77, plain, (![C_80, B_81]: (C_80=B_81 | k1_relat_1(C_80)!='#skF_8' | k1_relat_1(B_81)!='#skF_8' | ~v1_funct_1(C_80) | ~v1_relat_1(C_80) | ~v1_funct_1(B_81) | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.28/2.34  tff(c_81, plain, (![B_81, A_57]: (B_81='#skF_7'(A_57) | k1_relat_1('#skF_7'(A_57))!='#skF_8' | k1_relat_1(B_81)!='#skF_8' | ~v1_funct_1('#skF_7'(A_57)) | ~v1_funct_1(B_81) | ~v1_relat_1(B_81))), inference(resolution, [status(thm)], [c_42, c_77])).
% 6.28/2.34  tff(c_128, plain, (![B_97, A_98]: (B_97='#skF_7'(A_98) | A_98!='#skF_8' | k1_relat_1(B_97)!='#skF_8' | ~v1_funct_1(B_97) | ~v1_relat_1(B_97))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_81])).
% 6.28/2.34  tff(c_130, plain, (![A_98, A_50, B_51]: ('#skF_7'(A_98)='#skF_6'(A_50, B_51) | A_98!='#skF_8' | k1_relat_1('#skF_6'(A_50, B_51))!='#skF_8' | ~v1_funct_1('#skF_6'(A_50, B_51)))), inference(resolution, [status(thm)], [c_34, c_128])).
% 6.28/2.34  tff(c_209, plain, (![A_106, A_107, B_108]: ('#skF_7'(A_106)='#skF_6'(A_107, B_108) | A_106!='#skF_8' | A_107!='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_130])).
% 6.28/2.34  tff(c_28, plain, (![A_50, B_51, D_56]: (k1_funct_1('#skF_6'(A_50, B_51), D_56)=B_51 | ~r2_hidden(D_56, A_50))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.28/2.34  tff(c_224, plain, (![A_106, D_56, B_108, A_107]: (k1_funct_1('#skF_7'(A_106), D_56)=B_108 | ~r2_hidden(D_56, A_107) | A_106!='#skF_8' | A_107!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_209, c_28])).
% 6.28/2.34  tff(c_5003, plain, (![A_3145, A_3146, C_3147]: (k1_funct_1('#skF_7'(A_3145), '#skF_4'(A_3146, k1_xboole_0, C_3147))='#skF_8' | A_3145!='#skF_8' | C_3147!='#skF_8' | k9_relat_1(A_3146, k1_xboole_0)=C_3147 | ~v1_relat_1(A_3146))), inference(resolution, [status(thm)], [c_3305, c_224])).
% 6.28/2.34  tff(c_36, plain, (![A_57, C_62]: (k1_funct_1('#skF_7'(A_57), C_62)=k1_xboole_0 | ~r2_hidden(C_62, A_57))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.28/2.34  tff(c_5006, plain, (![A_3146, C_3147, A_3145]: (k1_xboole_0='#skF_8' | ~r2_hidden('#skF_4'(A_3146, k1_xboole_0, C_3147), A_3145) | A_3145!='#skF_8' | C_3147!='#skF_8' | k9_relat_1(A_3146, k1_xboole_0)=C_3147 | ~v1_relat_1(A_3146))), inference(superposition, [status(thm), theory('equality')], [c_5003, c_36])).
% 6.28/2.34  tff(c_5133, plain, (![A_5741, C_5742, A_5743]: (~r2_hidden('#skF_4'(A_5741, k1_xboole_0, C_5742), A_5743) | A_5743!='#skF_8' | C_5742!='#skF_8' | k9_relat_1(A_5741, k1_xboole_0)=C_5742 | ~v1_relat_1(A_5741))), inference(negUnitSimplification, [status(thm)], [c_44, c_5006])).
% 6.28/2.34  tff(c_5152, plain, (![C_3034, A_3033]: (C_3034!='#skF_8' | k9_relat_1(A_3033, k1_xboole_0)=C_3034 | ~v1_relat_1(A_3033))), inference(resolution, [status(thm)], [c_3302, c_5133])).
% 6.28/2.34  tff(c_5223, plain, (![A_5805]: (k9_relat_1(A_5805, k1_xboole_0)='#skF_8' | ~v1_relat_1(A_5805))), inference(reflexivity, [status(thm), theory('equality')], [c_5152])).
% 6.28/2.34  tff(c_5231, plain, (![A_57]: (k9_relat_1('#skF_7'(A_57), k1_xboole_0)='#skF_8')), inference(resolution, [status(thm)], [c_42, c_5223])).
% 6.28/2.34  tff(c_502, plain, (![A_57]: (k9_relat_1('#skF_7'(A_57), k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_494])).
% 6.28/2.34  tff(c_5232, plain, (k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_5231, c_502])).
% 6.28/2.34  tff(c_5234, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_5232])).
% 6.28/2.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.28/2.34  
% 6.28/2.34  Inference rules
% 6.28/2.34  ----------------------
% 6.28/2.34  #Ref     : 3
% 6.28/2.34  #Sup     : 1259
% 6.28/2.34  #Fact    : 0
% 6.28/2.34  #Define  : 0
% 6.28/2.34  #Split   : 2
% 6.28/2.34  #Chain   : 0
% 6.28/2.34  #Close   : 0
% 6.28/2.34  
% 6.28/2.34  Ordering : KBO
% 6.28/2.34  
% 6.28/2.34  Simplification rules
% 6.28/2.34  ----------------------
% 6.28/2.34  #Subsume      : 504
% 6.28/2.34  #Demod        : 317
% 6.28/2.34  #Tautology    : 109
% 6.28/2.34  #SimpNegUnit  : 9
% 6.28/2.34  #BackRed      : 1
% 6.28/2.34  
% 6.28/2.34  #Partial instantiations: 2786
% 6.28/2.34  #Strategies tried      : 1
% 6.28/2.34  
% 6.28/2.34  Timing (in seconds)
% 6.28/2.34  ----------------------
% 6.28/2.34  Preprocessing        : 0.33
% 6.28/2.35  Parsing              : 0.17
% 6.28/2.35  CNF conversion       : 0.03
% 6.28/2.35  Main loop            : 1.20
% 6.28/2.35  Inferencing          : 0.40
% 6.28/2.35  Reduction            : 0.30
% 6.28/2.35  Demodulation         : 0.21
% 6.28/2.35  BG Simplification    : 0.04
% 6.28/2.35  Subsumption          : 0.40
% 6.28/2.35  Abstraction          : 0.05
% 6.28/2.35  MUC search           : 0.00
% 6.28/2.35  Cooper               : 0.00
% 6.28/2.35  Total                : 1.56
% 6.28/2.35  Index Insertion      : 0.00
% 6.28/2.35  Index Deletion       : 0.00
% 6.28/2.35  Index Matching       : 0.00
% 6.28/2.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
