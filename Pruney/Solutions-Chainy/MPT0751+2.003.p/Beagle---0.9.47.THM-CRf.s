%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:25 EST 2020

% Result     : Theorem 20.53s
% Output     : CNFRefutation 20.53s
% Verified   : 
% Statistics : Number of formulae       :  120 (1037 expanded)
%              Number of leaves         :   34 ( 361 expanded)
%              Depth                    :   15
%              Number of atoms          :  244 (2729 expanded)
%              Number of equality atoms :   17 ( 291 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v4_ordinal1 > v3_ordinal1 > k2_xboole_0 > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_7 > #skF_8 > #skF_3 > #skF_10 > #skF_5 > #skF_9 > #skF_2 > #skF_1 > #skF_6 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(v4_ordinal1,type,(
    v4_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_162,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ( ~ ( ~ v4_ordinal1(A)
              & ! [B] :
                  ( v3_ordinal1(B)
                 => A != k1_ordinal1(B) ) )
          & ~ ( ? [B] :
                  ( v3_ordinal1(B)
                  & A = k1_ordinal1(B) )
              & v4_ordinal1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_ordinal1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v3_ordinal1(B)
     => ( r2_hidden(A,B)
       => v3_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).

tff(f_74,axiom,(
    ! [A] :
    ? [B] :
    ! [C] :
      ( r2_hidden(C,B)
    <=> ( r2_hidden(C,A)
        & v3_ordinal1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s1_xboole_0__e3_53__ordinal1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_136,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v4_ordinal1(A)
      <=> ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(B,A)
             => r2_hidden(k1_ordinal1(B),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_ordinal1)).

tff(f_101,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k1_ordinal1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_141,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_97,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_119,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_hidden(A,k1_ordinal1(B))
          <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_76,axiom,(
    ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

tff(c_76,plain,(
    v3_ordinal1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_88,plain,
    ( ~ v4_ordinal1('#skF_9')
    | v3_ordinal1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_93,plain,(
    ~ v4_ordinal1('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_28159,plain,(
    ! [A_734,B_735] :
      ( r2_hidden('#skF_1'(A_734,B_735),A_734)
      | r1_tarski(A_734,B_735) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_48,plain,(
    ! [A_39,B_40] :
      ( v3_ordinal1(A_39)
      | ~ r2_hidden(A_39,B_40)
      | ~ v3_ordinal1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_28180,plain,(
    ! [A_734,B_735] :
      ( v3_ordinal1('#skF_1'(A_734,B_735))
      | ~ v3_ordinal1(A_734)
      | r1_tarski(A_734,B_735) ) ),
    inference(resolution,[status(thm)],[c_28159,c_48])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_28224,plain,(
    ! [C_747,A_748] :
      ( r2_hidden(C_747,'#skF_6'(A_748))
      | ~ v3_ordinal1(C_747)
      | ~ r2_hidden(C_747,A_748) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_42372,plain,(
    ! [A_1212,A_1213] :
      ( r1_tarski(A_1212,'#skF_6'(A_1213))
      | ~ v3_ordinal1('#skF_1'(A_1212,'#skF_6'(A_1213)))
      | ~ r2_hidden('#skF_1'(A_1212,'#skF_6'(A_1213)),A_1213) ) ),
    inference(resolution,[status(thm)],[c_28224,c_4])).

tff(c_42459,plain,(
    ! [A_1214] :
      ( ~ v3_ordinal1('#skF_1'(A_1214,'#skF_6'(A_1214)))
      | r1_tarski(A_1214,'#skF_6'(A_1214)) ) ),
    inference(resolution,[status(thm)],[c_6,c_42372])).

tff(c_42480,plain,(
    ! [A_1215] :
      ( ~ v3_ordinal1(A_1215)
      | r1_tarski(A_1215,'#skF_6'(A_1215)) ) ),
    inference(resolution,[status(thm)],[c_28180,c_42459])).

tff(c_44,plain,(
    ! [C_37,A_32] :
      ( r2_hidden(C_37,A_32)
      | ~ r2_hidden(C_37,'#skF_6'(A_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_29705,plain,(
    ! [A_836,B_837] :
      ( r2_hidden('#skF_1'('#skF_6'(A_836),B_837),A_836)
      | r1_tarski('#skF_6'(A_836),B_837) ) ),
    inference(resolution,[status(thm)],[c_28159,c_44])).

tff(c_29740,plain,(
    ! [A_838] : r1_tarski('#skF_6'(A_838),A_838) ),
    inference(resolution,[status(thm)],[c_29705,c_4])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_29751,plain,(
    ! [A_838] :
      ( '#skF_6'(A_838) = A_838
      | ~ r1_tarski(A_838,'#skF_6'(A_838)) ) ),
    inference(resolution,[status(thm)],[c_29740,c_8])).

tff(c_42593,plain,(
    ! [A_1216] :
      ( '#skF_6'(A_1216) = A_1216
      | ~ v3_ordinal1(A_1216) ) ),
    inference(resolution,[status(thm)],[c_42480,c_29751])).

tff(c_42637,plain,(
    '#skF_6'('#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_76,c_42593])).

tff(c_28184,plain,(
    ! [A_736] :
      ( r2_hidden('#skF_8'(A_736),A_736)
      | v4_ordinal1(A_736)
      | ~ v3_ordinal1(A_736) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_28200,plain,(
    ! [A_32] :
      ( r2_hidden('#skF_8'('#skF_6'(A_32)),A_32)
      | v4_ordinal1('#skF_6'(A_32))
      | ~ v3_ordinal1('#skF_6'(A_32)) ) ),
    inference(resolution,[status(thm)],[c_28184,c_44])).

tff(c_42850,plain,
    ( r2_hidden('#skF_8'('#skF_9'),'#skF_9')
    | v4_ordinal1('#skF_6'('#skF_9'))
    | ~ v3_ordinal1('#skF_6'('#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_42637,c_28200])).

tff(c_43013,plain,
    ( r2_hidden('#skF_8'('#skF_9'),'#skF_9')
    | v4_ordinal1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_42637,c_42637,c_42850])).

tff(c_43014,plain,(
    r2_hidden('#skF_8'('#skF_9'),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_43013])).

tff(c_43511,plain,
    ( v3_ordinal1('#skF_8'('#skF_9'))
    | ~ v3_ordinal1('#skF_9') ),
    inference(resolution,[status(thm)],[c_43014,c_48])).

tff(c_43526,plain,(
    v3_ordinal1('#skF_8'('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_43511])).

tff(c_52,plain,(
    ! [A_44] :
      ( v3_ordinal1(k1_ordinal1(A_44))
      | ~ v3_ordinal1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_78,plain,(
    ! [B_61] :
      ( k1_ordinal1(B_61) != '#skF_9'
      | ~ v3_ordinal1(B_61)
      | v4_ordinal1('#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_28115,plain,(
    ! [B_61] :
      ( k1_ordinal1(B_61) != '#skF_9'
      | ~ v3_ordinal1(B_61) ) ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_78])).

tff(c_44181,plain,(
    k1_ordinal1('#skF_8'('#skF_9')) != '#skF_9' ),
    inference(resolution,[status(thm)],[c_43526,c_28115])).

tff(c_38,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(A_30,B_31)
      | ~ r1_ordinal1(A_30,B_31)
      | ~ v3_ordinal1(B_31)
      | ~ v3_ordinal1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_30312,plain,(
    ! [A_872] :
      ( r2_hidden('#skF_8'('#skF_6'(A_872)),A_872)
      | v4_ordinal1('#skF_6'(A_872))
      | ~ v3_ordinal1('#skF_6'(A_872)) ) ),
    inference(resolution,[status(thm)],[c_28184,c_44])).

tff(c_74,plain,(
    ! [B_58,A_57] :
      ( ~ r1_tarski(B_58,A_57)
      | ~ r2_hidden(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_30340,plain,(
    ! [A_872] :
      ( ~ r1_tarski(A_872,'#skF_8'('#skF_6'(A_872)))
      | v4_ordinal1('#skF_6'(A_872))
      | ~ v3_ordinal1('#skF_6'(A_872)) ) ),
    inference(resolution,[status(thm)],[c_30312,c_74])).

tff(c_42837,plain,
    ( ~ r1_tarski('#skF_9','#skF_8'('#skF_9'))
    | v4_ordinal1('#skF_6'('#skF_9'))
    | ~ v3_ordinal1('#skF_6'('#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_42637,c_30340])).

tff(c_43008,plain,
    ( ~ r1_tarski('#skF_9','#skF_8'('#skF_9'))
    | v4_ordinal1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_42637,c_42637,c_42837])).

tff(c_43009,plain,(
    ~ r1_tarski('#skF_9','#skF_8'('#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_43008])).

tff(c_44184,plain,
    ( ~ r1_ordinal1('#skF_9','#skF_8'('#skF_9'))
    | ~ v3_ordinal1('#skF_8'('#skF_9'))
    | ~ v3_ordinal1('#skF_9') ),
    inference(resolution,[status(thm)],[c_38,c_43009])).

tff(c_44187,plain,(
    ~ r1_ordinal1('#skF_9','#skF_8'('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_43526,c_44184])).

tff(c_29072,plain,(
    ! [B_820,A_821] :
      ( r2_hidden(B_820,A_821)
      | B_820 = A_821
      | r2_hidden(A_821,B_820)
      | ~ v3_ordinal1(B_820)
      | ~ v3_ordinal1(A_821) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_60,plain,(
    ! [A_48,B_50] :
      ( r1_ordinal1(A_48,B_50)
      | ~ r2_hidden(A_48,k1_ordinal1(B_50))
      | ~ v3_ordinal1(B_50)
      | ~ v3_ordinal1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_57103,plain,(
    ! [A_1342,B_1343] :
      ( r1_ordinal1(A_1342,B_1343)
      | ~ v3_ordinal1(B_1343)
      | r2_hidden(k1_ordinal1(B_1343),A_1342)
      | k1_ordinal1(B_1343) = A_1342
      | ~ v3_ordinal1(k1_ordinal1(B_1343))
      | ~ v3_ordinal1(A_1342) ) ),
    inference(resolution,[status(thm)],[c_29072,c_60])).

tff(c_68,plain,(
    ! [A_53] :
      ( ~ r2_hidden(k1_ordinal1('#skF_8'(A_53)),A_53)
      | v4_ordinal1(A_53)
      | ~ v3_ordinal1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_56344,plain,(
    ! [A_1332] :
      ( v4_ordinal1('#skF_6'(A_1332))
      | ~ v3_ordinal1('#skF_6'(A_1332))
      | ~ v3_ordinal1(k1_ordinal1('#skF_8'('#skF_6'(A_1332))))
      | ~ r2_hidden(k1_ordinal1('#skF_8'('#skF_6'(A_1332))),A_1332) ) ),
    inference(resolution,[status(thm)],[c_28224,c_68])).

tff(c_56404,plain,
    ( v4_ordinal1('#skF_6'('#skF_9'))
    | ~ v3_ordinal1('#skF_6'('#skF_9'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_8'('#skF_6'('#skF_9'))))
    | ~ r2_hidden(k1_ordinal1('#skF_8'('#skF_9')),'#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_42637,c_56344])).

tff(c_56481,plain,
    ( v4_ordinal1('#skF_9')
    | ~ v3_ordinal1(k1_ordinal1('#skF_8'('#skF_9')))
    | ~ r2_hidden(k1_ordinal1('#skF_8'('#skF_9')),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42637,c_76,c_42637,c_42637,c_56404])).

tff(c_56482,plain,
    ( ~ v3_ordinal1(k1_ordinal1('#skF_8'('#skF_9')))
    | ~ r2_hidden(k1_ordinal1('#skF_8'('#skF_9')),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_56481])).

tff(c_56562,plain,(
    ~ r2_hidden(k1_ordinal1('#skF_8'('#skF_9')),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_56482])).

tff(c_57110,plain,
    ( r1_ordinal1('#skF_9','#skF_8'('#skF_9'))
    | ~ v3_ordinal1('#skF_8'('#skF_9'))
    | k1_ordinal1('#skF_8'('#skF_9')) = '#skF_9'
    | ~ v3_ordinal1(k1_ordinal1('#skF_8'('#skF_9')))
    | ~ v3_ordinal1('#skF_9') ),
    inference(resolution,[status(thm)],[c_57103,c_56562])).

tff(c_57351,plain,
    ( r1_ordinal1('#skF_9','#skF_8'('#skF_9'))
    | k1_ordinal1('#skF_8'('#skF_9')) = '#skF_9'
    | ~ v3_ordinal1(k1_ordinal1('#skF_8'('#skF_9'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_43526,c_57110])).

tff(c_57352,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_8'('#skF_9'))) ),
    inference(negUnitSimplification,[status(thm)],[c_44181,c_44187,c_57351])).

tff(c_57450,plain,(
    ~ v3_ordinal1('#skF_8'('#skF_9')) ),
    inference(resolution,[status(thm)],[c_52,c_57352])).

tff(c_57454,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_43526,c_57450])).

tff(c_57455,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_8'('#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_56482])).

tff(c_57459,plain,(
    ~ v3_ordinal1('#skF_8'('#skF_9')) ),
    inference(resolution,[status(thm)],[c_52,c_57455])).

tff(c_57463,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_43526,c_57459])).

tff(c_57464,plain,(
    v3_ordinal1('#skF_10') ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_57765,plain,(
    ! [A_1399,B_1400] :
      ( r1_tarski(A_1399,B_1400)
      | ~ r1_ordinal1(A_1399,B_1400)
      | ~ v3_ordinal1(B_1400)
      | ~ v3_ordinal1(A_1399) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_57465,plain,(
    v4_ordinal1('#skF_9') ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_84,plain,
    ( ~ v4_ordinal1('#skF_9')
    | k1_ordinal1('#skF_10') = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_57466,plain,(
    ~ v4_ordinal1('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_57468,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_57465,c_57466])).

tff(c_57469,plain,(
    k1_ordinal1('#skF_10') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_46,plain,(
    ! [A_38] : r2_hidden(A_38,k1_ordinal1(A_38)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_57475,plain,(
    r2_hidden('#skF_10','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_57469,c_46])).

tff(c_57486,plain,(
    ! [B_1346,A_1347] :
      ( ~ r1_tarski(B_1346,A_1347)
      | ~ r2_hidden(A_1347,B_1346) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_57493,plain,(
    ~ r1_tarski('#skF_9','#skF_10') ),
    inference(resolution,[status(thm)],[c_57475,c_57486])).

tff(c_57801,plain,
    ( ~ r1_ordinal1('#skF_9','#skF_10')
    | ~ v3_ordinal1('#skF_10')
    | ~ v3_ordinal1('#skF_9') ),
    inference(resolution,[status(thm)],[c_57765,c_57493])).

tff(c_57818,plain,(
    ~ r1_ordinal1('#skF_9','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_57464,c_57801])).

tff(c_58528,plain,(
    ! [A_1428,B_1429] :
      ( r1_ordinal1(A_1428,B_1429)
      | ~ r2_hidden(A_1428,k1_ordinal1(B_1429))
      | ~ v3_ordinal1(B_1429)
      | ~ v3_ordinal1(A_1428) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_58550,plain,(
    ! [A_1428] :
      ( r1_ordinal1(A_1428,'#skF_10')
      | ~ r2_hidden(A_1428,'#skF_9')
      | ~ v3_ordinal1('#skF_10')
      | ~ v3_ordinal1(A_1428) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57469,c_58528])).

tff(c_58600,plain,(
    ! [A_1430] :
      ( r1_ordinal1(A_1430,'#skF_10')
      | ~ r2_hidden(A_1430,'#skF_9')
      | ~ v3_ordinal1(A_1430) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57464,c_58550])).

tff(c_58622,plain,
    ( r1_ordinal1('#skF_10','#skF_10')
    | ~ v3_ordinal1('#skF_10') ),
    inference(resolution,[status(thm)],[c_57475,c_58600])).

tff(c_58634,plain,(
    r1_ordinal1('#skF_10','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57464,c_58622])).

tff(c_58185,plain,(
    ! [A_1421,B_1422] :
      ( r2_hidden(A_1421,k1_ordinal1(B_1422))
      | ~ r1_ordinal1(A_1421,B_1422)
      | ~ v3_ordinal1(B_1422)
      | ~ v3_ordinal1(A_1421) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_58262,plain,(
    ! [A_1421] :
      ( r2_hidden(A_1421,'#skF_9')
      | ~ r1_ordinal1(A_1421,'#skF_10')
      | ~ v3_ordinal1('#skF_10')
      | ~ v3_ordinal1(A_1421) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57469,c_58185])).

tff(c_58304,plain,(
    ! [A_1421] :
      ( r2_hidden(A_1421,'#skF_9')
      | ~ r1_ordinal1(A_1421,'#skF_10')
      | ~ v3_ordinal1(A_1421) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57464,c_58262])).

tff(c_59519,plain,(
    ! [B_1448,A_1449] :
      ( r2_hidden(k1_ordinal1(B_1448),A_1449)
      | ~ r2_hidden(B_1448,A_1449)
      | ~ v3_ordinal1(B_1448)
      | ~ v4_ordinal1(A_1449)
      | ~ v3_ordinal1(A_1449) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_59552,plain,(
    ! [A_1449] :
      ( r2_hidden('#skF_9',A_1449)
      | ~ r2_hidden('#skF_10',A_1449)
      | ~ v3_ordinal1('#skF_10')
      | ~ v4_ordinal1(A_1449)
      | ~ v3_ordinal1(A_1449) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57469,c_59519])).

tff(c_59606,plain,(
    ! [A_1451] :
      ( r2_hidden('#skF_9',A_1451)
      | ~ r2_hidden('#skF_10',A_1451)
      | ~ v4_ordinal1(A_1451)
      | ~ v3_ordinal1(A_1451) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57464,c_59552])).

tff(c_59629,plain,
    ( r2_hidden('#skF_9','#skF_9')
    | ~ v4_ordinal1('#skF_9')
    | ~ v3_ordinal1('#skF_9')
    | ~ r1_ordinal1('#skF_10','#skF_10')
    | ~ v3_ordinal1('#skF_10') ),
    inference(resolution,[status(thm)],[c_58304,c_59606])).

tff(c_59669,plain,(
    r2_hidden('#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57464,c_58634,c_76,c_57465,c_59629])).

tff(c_58562,plain,(
    ! [A_1428] :
      ( r1_ordinal1(A_1428,'#skF_10')
      | ~ r2_hidden(A_1428,'#skF_9')
      | ~ v3_ordinal1(A_1428) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57464,c_58550])).

tff(c_59687,plain,
    ( r1_ordinal1('#skF_9','#skF_10')
    | ~ v3_ordinal1('#skF_9') ),
    inference(resolution,[status(thm)],[c_59669,c_58562])).

tff(c_59700,plain,(
    r1_ordinal1('#skF_9','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_59687])).

tff(c_59702,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57818,c_59700])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:46:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 20.53/9.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.53/9.32  
% 20.53/9.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.53/9.32  %$ r2_hidden > r1_tarski > r1_ordinal1 > v4_ordinal1 > v3_ordinal1 > k2_xboole_0 > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_7 > #skF_8 > #skF_3 > #skF_10 > #skF_5 > #skF_9 > #skF_2 > #skF_1 > #skF_6 > #skF_4
% 20.53/9.32  
% 20.53/9.32  %Foreground sorts:
% 20.53/9.32  
% 20.53/9.32  
% 20.53/9.32  %Background operators:
% 20.53/9.32  
% 20.53/9.32  
% 20.53/9.32  %Foreground operators:
% 20.53/9.32  tff('#skF_7', type, '#skF_7': $i > $i).
% 20.53/9.32  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 20.53/9.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 20.53/9.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 20.53/9.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 20.53/9.32  tff('#skF_8', type, '#skF_8': $i > $i).
% 20.53/9.32  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 20.53/9.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 20.53/9.32  tff('#skF_10', type, '#skF_10': $i).
% 20.53/9.32  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 20.53/9.32  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 20.53/9.32  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 20.53/9.32  tff('#skF_9', type, '#skF_9': $i).
% 20.53/9.32  tff(v4_ordinal1, type, v4_ordinal1: $i > $o).
% 20.53/9.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 20.53/9.32  tff(k3_tarski, type, k3_tarski: $i > $i).
% 20.53/9.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 20.53/9.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 20.53/9.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 20.53/9.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 20.53/9.32  tff('#skF_6', type, '#skF_6': $i > $i).
% 20.53/9.32  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 20.53/9.32  
% 20.53/9.34  tff(f_162, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (~(~v4_ordinal1(A) & (![B]: (v3_ordinal1(B) => ~(A = k1_ordinal1(B))))) & ~((?[B]: (v3_ordinal1(B) & (A = k1_ordinal1(B)))) & v4_ordinal1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_ordinal1)).
% 20.53/9.34  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 20.53/9.34  tff(f_82, axiom, (![A, B]: (v3_ordinal1(B) => (r2_hidden(A, B) => v3_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_ordinal1)).
% 20.53/9.34  tff(f_74, axiom, (![A]: (?[B]: (![C]: (r2_hidden(C, B) <=> (r2_hidden(C, A) & v3_ordinal1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s1_xboole_0__e3_53__ordinal1)).
% 20.53/9.34  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 20.53/9.34  tff(f_136, axiom, (![A]: (v3_ordinal1(A) => (v4_ordinal1(A) <=> (![B]: (v3_ordinal1(B) => (r2_hidden(B, A) => r2_hidden(k1_ordinal1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_ordinal1)).
% 20.53/9.34  tff(f_101, axiom, (![A]: (v3_ordinal1(A) => v3_ordinal1(k1_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_ordinal1)).
% 20.53/9.34  tff(f_66, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 20.53/9.34  tff(f_141, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 20.53/9.34  tff(f_97, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_ordinal1)).
% 20.53/9.34  tff(f_119, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_ordinal1)).
% 20.53/9.34  tff(f_76, axiom, (![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_ordinal1)).
% 20.53/9.34  tff(c_76, plain, (v3_ordinal1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_162])).
% 20.53/9.34  tff(c_88, plain, (~v4_ordinal1('#skF_9') | v3_ordinal1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_162])).
% 20.53/9.34  tff(c_93, plain, (~v4_ordinal1('#skF_9')), inference(splitLeft, [status(thm)], [c_88])).
% 20.53/9.34  tff(c_28159, plain, (![A_734, B_735]: (r2_hidden('#skF_1'(A_734, B_735), A_734) | r1_tarski(A_734, B_735))), inference(cnfTransformation, [status(thm)], [f_32])).
% 20.53/9.34  tff(c_48, plain, (![A_39, B_40]: (v3_ordinal1(A_39) | ~r2_hidden(A_39, B_40) | ~v3_ordinal1(B_40))), inference(cnfTransformation, [status(thm)], [f_82])).
% 20.53/9.34  tff(c_28180, plain, (![A_734, B_735]: (v3_ordinal1('#skF_1'(A_734, B_735)) | ~v3_ordinal1(A_734) | r1_tarski(A_734, B_735))), inference(resolution, [status(thm)], [c_28159, c_48])).
% 20.53/9.34  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 20.53/9.34  tff(c_28224, plain, (![C_747, A_748]: (r2_hidden(C_747, '#skF_6'(A_748)) | ~v3_ordinal1(C_747) | ~r2_hidden(C_747, A_748))), inference(cnfTransformation, [status(thm)], [f_74])).
% 20.53/9.34  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 20.53/9.34  tff(c_42372, plain, (![A_1212, A_1213]: (r1_tarski(A_1212, '#skF_6'(A_1213)) | ~v3_ordinal1('#skF_1'(A_1212, '#skF_6'(A_1213))) | ~r2_hidden('#skF_1'(A_1212, '#skF_6'(A_1213)), A_1213))), inference(resolution, [status(thm)], [c_28224, c_4])).
% 20.53/9.34  tff(c_42459, plain, (![A_1214]: (~v3_ordinal1('#skF_1'(A_1214, '#skF_6'(A_1214))) | r1_tarski(A_1214, '#skF_6'(A_1214)))), inference(resolution, [status(thm)], [c_6, c_42372])).
% 20.53/9.34  tff(c_42480, plain, (![A_1215]: (~v3_ordinal1(A_1215) | r1_tarski(A_1215, '#skF_6'(A_1215)))), inference(resolution, [status(thm)], [c_28180, c_42459])).
% 20.53/9.34  tff(c_44, plain, (![C_37, A_32]: (r2_hidden(C_37, A_32) | ~r2_hidden(C_37, '#skF_6'(A_32)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 20.53/9.34  tff(c_29705, plain, (![A_836, B_837]: (r2_hidden('#skF_1'('#skF_6'(A_836), B_837), A_836) | r1_tarski('#skF_6'(A_836), B_837))), inference(resolution, [status(thm)], [c_28159, c_44])).
% 20.53/9.34  tff(c_29740, plain, (![A_838]: (r1_tarski('#skF_6'(A_838), A_838))), inference(resolution, [status(thm)], [c_29705, c_4])).
% 20.53/9.34  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 20.53/9.34  tff(c_29751, plain, (![A_838]: ('#skF_6'(A_838)=A_838 | ~r1_tarski(A_838, '#skF_6'(A_838)))), inference(resolution, [status(thm)], [c_29740, c_8])).
% 20.53/9.34  tff(c_42593, plain, (![A_1216]: ('#skF_6'(A_1216)=A_1216 | ~v3_ordinal1(A_1216))), inference(resolution, [status(thm)], [c_42480, c_29751])).
% 20.53/9.34  tff(c_42637, plain, ('#skF_6'('#skF_9')='#skF_9'), inference(resolution, [status(thm)], [c_76, c_42593])).
% 20.53/9.34  tff(c_28184, plain, (![A_736]: (r2_hidden('#skF_8'(A_736), A_736) | v4_ordinal1(A_736) | ~v3_ordinal1(A_736))), inference(cnfTransformation, [status(thm)], [f_136])).
% 20.53/9.34  tff(c_28200, plain, (![A_32]: (r2_hidden('#skF_8'('#skF_6'(A_32)), A_32) | v4_ordinal1('#skF_6'(A_32)) | ~v3_ordinal1('#skF_6'(A_32)))), inference(resolution, [status(thm)], [c_28184, c_44])).
% 20.53/9.34  tff(c_42850, plain, (r2_hidden('#skF_8'('#skF_9'), '#skF_9') | v4_ordinal1('#skF_6'('#skF_9')) | ~v3_ordinal1('#skF_6'('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_42637, c_28200])).
% 20.53/9.34  tff(c_43013, plain, (r2_hidden('#skF_8'('#skF_9'), '#skF_9') | v4_ordinal1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_42637, c_42637, c_42850])).
% 20.53/9.34  tff(c_43014, plain, (r2_hidden('#skF_8'('#skF_9'), '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_93, c_43013])).
% 20.53/9.34  tff(c_43511, plain, (v3_ordinal1('#skF_8'('#skF_9')) | ~v3_ordinal1('#skF_9')), inference(resolution, [status(thm)], [c_43014, c_48])).
% 20.53/9.34  tff(c_43526, plain, (v3_ordinal1('#skF_8'('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_43511])).
% 20.53/9.34  tff(c_52, plain, (![A_44]: (v3_ordinal1(k1_ordinal1(A_44)) | ~v3_ordinal1(A_44))), inference(cnfTransformation, [status(thm)], [f_101])).
% 20.53/9.34  tff(c_78, plain, (![B_61]: (k1_ordinal1(B_61)!='#skF_9' | ~v3_ordinal1(B_61) | v4_ordinal1('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_162])).
% 20.53/9.34  tff(c_28115, plain, (![B_61]: (k1_ordinal1(B_61)!='#skF_9' | ~v3_ordinal1(B_61))), inference(negUnitSimplification, [status(thm)], [c_93, c_78])).
% 20.53/9.34  tff(c_44181, plain, (k1_ordinal1('#skF_8'('#skF_9'))!='#skF_9'), inference(resolution, [status(thm)], [c_43526, c_28115])).
% 20.53/9.34  tff(c_38, plain, (![A_30, B_31]: (r1_tarski(A_30, B_31) | ~r1_ordinal1(A_30, B_31) | ~v3_ordinal1(B_31) | ~v3_ordinal1(A_30))), inference(cnfTransformation, [status(thm)], [f_66])).
% 20.53/9.34  tff(c_30312, plain, (![A_872]: (r2_hidden('#skF_8'('#skF_6'(A_872)), A_872) | v4_ordinal1('#skF_6'(A_872)) | ~v3_ordinal1('#skF_6'(A_872)))), inference(resolution, [status(thm)], [c_28184, c_44])).
% 20.53/9.34  tff(c_74, plain, (![B_58, A_57]: (~r1_tarski(B_58, A_57) | ~r2_hidden(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_141])).
% 20.53/9.34  tff(c_30340, plain, (![A_872]: (~r1_tarski(A_872, '#skF_8'('#skF_6'(A_872))) | v4_ordinal1('#skF_6'(A_872)) | ~v3_ordinal1('#skF_6'(A_872)))), inference(resolution, [status(thm)], [c_30312, c_74])).
% 20.53/9.34  tff(c_42837, plain, (~r1_tarski('#skF_9', '#skF_8'('#skF_9')) | v4_ordinal1('#skF_6'('#skF_9')) | ~v3_ordinal1('#skF_6'('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_42637, c_30340])).
% 20.53/9.34  tff(c_43008, plain, (~r1_tarski('#skF_9', '#skF_8'('#skF_9')) | v4_ordinal1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_42637, c_42637, c_42837])).
% 20.53/9.34  tff(c_43009, plain, (~r1_tarski('#skF_9', '#skF_8'('#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_93, c_43008])).
% 20.53/9.34  tff(c_44184, plain, (~r1_ordinal1('#skF_9', '#skF_8'('#skF_9')) | ~v3_ordinal1('#skF_8'('#skF_9')) | ~v3_ordinal1('#skF_9')), inference(resolution, [status(thm)], [c_38, c_43009])).
% 20.53/9.34  tff(c_44187, plain, (~r1_ordinal1('#skF_9', '#skF_8'('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_43526, c_44184])).
% 20.53/9.34  tff(c_29072, plain, (![B_820, A_821]: (r2_hidden(B_820, A_821) | B_820=A_821 | r2_hidden(A_821, B_820) | ~v3_ordinal1(B_820) | ~v3_ordinal1(A_821))), inference(cnfTransformation, [status(thm)], [f_97])).
% 20.53/9.34  tff(c_60, plain, (![A_48, B_50]: (r1_ordinal1(A_48, B_50) | ~r2_hidden(A_48, k1_ordinal1(B_50)) | ~v3_ordinal1(B_50) | ~v3_ordinal1(A_48))), inference(cnfTransformation, [status(thm)], [f_119])).
% 20.53/9.34  tff(c_57103, plain, (![A_1342, B_1343]: (r1_ordinal1(A_1342, B_1343) | ~v3_ordinal1(B_1343) | r2_hidden(k1_ordinal1(B_1343), A_1342) | k1_ordinal1(B_1343)=A_1342 | ~v3_ordinal1(k1_ordinal1(B_1343)) | ~v3_ordinal1(A_1342))), inference(resolution, [status(thm)], [c_29072, c_60])).
% 20.53/9.34  tff(c_68, plain, (![A_53]: (~r2_hidden(k1_ordinal1('#skF_8'(A_53)), A_53) | v4_ordinal1(A_53) | ~v3_ordinal1(A_53))), inference(cnfTransformation, [status(thm)], [f_136])).
% 20.53/9.34  tff(c_56344, plain, (![A_1332]: (v4_ordinal1('#skF_6'(A_1332)) | ~v3_ordinal1('#skF_6'(A_1332)) | ~v3_ordinal1(k1_ordinal1('#skF_8'('#skF_6'(A_1332)))) | ~r2_hidden(k1_ordinal1('#skF_8'('#skF_6'(A_1332))), A_1332))), inference(resolution, [status(thm)], [c_28224, c_68])).
% 20.53/9.34  tff(c_56404, plain, (v4_ordinal1('#skF_6'('#skF_9')) | ~v3_ordinal1('#skF_6'('#skF_9')) | ~v3_ordinal1(k1_ordinal1('#skF_8'('#skF_6'('#skF_9')))) | ~r2_hidden(k1_ordinal1('#skF_8'('#skF_9')), '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_42637, c_56344])).
% 20.53/9.34  tff(c_56481, plain, (v4_ordinal1('#skF_9') | ~v3_ordinal1(k1_ordinal1('#skF_8'('#skF_9'))) | ~r2_hidden(k1_ordinal1('#skF_8'('#skF_9')), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_42637, c_76, c_42637, c_42637, c_56404])).
% 20.53/9.34  tff(c_56482, plain, (~v3_ordinal1(k1_ordinal1('#skF_8'('#skF_9'))) | ~r2_hidden(k1_ordinal1('#skF_8'('#skF_9')), '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_93, c_56481])).
% 20.53/9.34  tff(c_56562, plain, (~r2_hidden(k1_ordinal1('#skF_8'('#skF_9')), '#skF_9')), inference(splitLeft, [status(thm)], [c_56482])).
% 20.53/9.34  tff(c_57110, plain, (r1_ordinal1('#skF_9', '#skF_8'('#skF_9')) | ~v3_ordinal1('#skF_8'('#skF_9')) | k1_ordinal1('#skF_8'('#skF_9'))='#skF_9' | ~v3_ordinal1(k1_ordinal1('#skF_8'('#skF_9'))) | ~v3_ordinal1('#skF_9')), inference(resolution, [status(thm)], [c_57103, c_56562])).
% 20.53/9.34  tff(c_57351, plain, (r1_ordinal1('#skF_9', '#skF_8'('#skF_9')) | k1_ordinal1('#skF_8'('#skF_9'))='#skF_9' | ~v3_ordinal1(k1_ordinal1('#skF_8'('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_43526, c_57110])).
% 20.53/9.34  tff(c_57352, plain, (~v3_ordinal1(k1_ordinal1('#skF_8'('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_44181, c_44187, c_57351])).
% 20.53/9.34  tff(c_57450, plain, (~v3_ordinal1('#skF_8'('#skF_9'))), inference(resolution, [status(thm)], [c_52, c_57352])).
% 20.53/9.34  tff(c_57454, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_43526, c_57450])).
% 20.53/9.34  tff(c_57455, plain, (~v3_ordinal1(k1_ordinal1('#skF_8'('#skF_9')))), inference(splitRight, [status(thm)], [c_56482])).
% 20.53/9.34  tff(c_57459, plain, (~v3_ordinal1('#skF_8'('#skF_9'))), inference(resolution, [status(thm)], [c_52, c_57455])).
% 20.53/9.34  tff(c_57463, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_43526, c_57459])).
% 20.53/9.34  tff(c_57464, plain, (v3_ordinal1('#skF_10')), inference(splitRight, [status(thm)], [c_88])).
% 20.53/9.34  tff(c_57765, plain, (![A_1399, B_1400]: (r1_tarski(A_1399, B_1400) | ~r1_ordinal1(A_1399, B_1400) | ~v3_ordinal1(B_1400) | ~v3_ordinal1(A_1399))), inference(cnfTransformation, [status(thm)], [f_66])).
% 20.53/9.34  tff(c_57465, plain, (v4_ordinal1('#skF_9')), inference(splitRight, [status(thm)], [c_88])).
% 20.53/9.34  tff(c_84, plain, (~v4_ordinal1('#skF_9') | k1_ordinal1('#skF_10')='#skF_9'), inference(cnfTransformation, [status(thm)], [f_162])).
% 20.53/9.34  tff(c_57466, plain, (~v4_ordinal1('#skF_9')), inference(splitLeft, [status(thm)], [c_84])).
% 20.53/9.34  tff(c_57468, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_57465, c_57466])).
% 20.53/9.34  tff(c_57469, plain, (k1_ordinal1('#skF_10')='#skF_9'), inference(splitRight, [status(thm)], [c_84])).
% 20.53/9.34  tff(c_46, plain, (![A_38]: (r2_hidden(A_38, k1_ordinal1(A_38)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 20.53/9.34  tff(c_57475, plain, (r2_hidden('#skF_10', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_57469, c_46])).
% 20.53/9.34  tff(c_57486, plain, (![B_1346, A_1347]: (~r1_tarski(B_1346, A_1347) | ~r2_hidden(A_1347, B_1346))), inference(cnfTransformation, [status(thm)], [f_141])).
% 20.53/9.34  tff(c_57493, plain, (~r1_tarski('#skF_9', '#skF_10')), inference(resolution, [status(thm)], [c_57475, c_57486])).
% 20.53/9.34  tff(c_57801, plain, (~r1_ordinal1('#skF_9', '#skF_10') | ~v3_ordinal1('#skF_10') | ~v3_ordinal1('#skF_9')), inference(resolution, [status(thm)], [c_57765, c_57493])).
% 20.53/9.34  tff(c_57818, plain, (~r1_ordinal1('#skF_9', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_57464, c_57801])).
% 20.53/9.34  tff(c_58528, plain, (![A_1428, B_1429]: (r1_ordinal1(A_1428, B_1429) | ~r2_hidden(A_1428, k1_ordinal1(B_1429)) | ~v3_ordinal1(B_1429) | ~v3_ordinal1(A_1428))), inference(cnfTransformation, [status(thm)], [f_119])).
% 20.53/9.34  tff(c_58550, plain, (![A_1428]: (r1_ordinal1(A_1428, '#skF_10') | ~r2_hidden(A_1428, '#skF_9') | ~v3_ordinal1('#skF_10') | ~v3_ordinal1(A_1428))), inference(superposition, [status(thm), theory('equality')], [c_57469, c_58528])).
% 20.53/9.34  tff(c_58600, plain, (![A_1430]: (r1_ordinal1(A_1430, '#skF_10') | ~r2_hidden(A_1430, '#skF_9') | ~v3_ordinal1(A_1430))), inference(demodulation, [status(thm), theory('equality')], [c_57464, c_58550])).
% 20.53/9.34  tff(c_58622, plain, (r1_ordinal1('#skF_10', '#skF_10') | ~v3_ordinal1('#skF_10')), inference(resolution, [status(thm)], [c_57475, c_58600])).
% 20.53/9.34  tff(c_58634, plain, (r1_ordinal1('#skF_10', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_57464, c_58622])).
% 20.53/9.34  tff(c_58185, plain, (![A_1421, B_1422]: (r2_hidden(A_1421, k1_ordinal1(B_1422)) | ~r1_ordinal1(A_1421, B_1422) | ~v3_ordinal1(B_1422) | ~v3_ordinal1(A_1421))), inference(cnfTransformation, [status(thm)], [f_119])).
% 20.53/9.34  tff(c_58262, plain, (![A_1421]: (r2_hidden(A_1421, '#skF_9') | ~r1_ordinal1(A_1421, '#skF_10') | ~v3_ordinal1('#skF_10') | ~v3_ordinal1(A_1421))), inference(superposition, [status(thm), theory('equality')], [c_57469, c_58185])).
% 20.53/9.34  tff(c_58304, plain, (![A_1421]: (r2_hidden(A_1421, '#skF_9') | ~r1_ordinal1(A_1421, '#skF_10') | ~v3_ordinal1(A_1421))), inference(demodulation, [status(thm), theory('equality')], [c_57464, c_58262])).
% 20.53/9.34  tff(c_59519, plain, (![B_1448, A_1449]: (r2_hidden(k1_ordinal1(B_1448), A_1449) | ~r2_hidden(B_1448, A_1449) | ~v3_ordinal1(B_1448) | ~v4_ordinal1(A_1449) | ~v3_ordinal1(A_1449))), inference(cnfTransformation, [status(thm)], [f_136])).
% 20.53/9.34  tff(c_59552, plain, (![A_1449]: (r2_hidden('#skF_9', A_1449) | ~r2_hidden('#skF_10', A_1449) | ~v3_ordinal1('#skF_10') | ~v4_ordinal1(A_1449) | ~v3_ordinal1(A_1449))), inference(superposition, [status(thm), theory('equality')], [c_57469, c_59519])).
% 20.53/9.34  tff(c_59606, plain, (![A_1451]: (r2_hidden('#skF_9', A_1451) | ~r2_hidden('#skF_10', A_1451) | ~v4_ordinal1(A_1451) | ~v3_ordinal1(A_1451))), inference(demodulation, [status(thm), theory('equality')], [c_57464, c_59552])).
% 20.53/9.34  tff(c_59629, plain, (r2_hidden('#skF_9', '#skF_9') | ~v4_ordinal1('#skF_9') | ~v3_ordinal1('#skF_9') | ~r1_ordinal1('#skF_10', '#skF_10') | ~v3_ordinal1('#skF_10')), inference(resolution, [status(thm)], [c_58304, c_59606])).
% 20.53/9.34  tff(c_59669, plain, (r2_hidden('#skF_9', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_57464, c_58634, c_76, c_57465, c_59629])).
% 20.53/9.34  tff(c_58562, plain, (![A_1428]: (r1_ordinal1(A_1428, '#skF_10') | ~r2_hidden(A_1428, '#skF_9') | ~v3_ordinal1(A_1428))), inference(demodulation, [status(thm), theory('equality')], [c_57464, c_58550])).
% 20.53/9.34  tff(c_59687, plain, (r1_ordinal1('#skF_9', '#skF_10') | ~v3_ordinal1('#skF_9')), inference(resolution, [status(thm)], [c_59669, c_58562])).
% 20.53/9.34  tff(c_59700, plain, (r1_ordinal1('#skF_9', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_59687])).
% 20.53/9.34  tff(c_59702, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57818, c_59700])).
% 20.53/9.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.53/9.34  
% 20.53/9.34  Inference rules
% 20.53/9.34  ----------------------
% 20.53/9.34  #Ref     : 0
% 20.53/9.34  #Sup     : 12409
% 20.53/9.34  #Fact    : 12
% 20.53/9.34  #Define  : 0
% 20.53/9.34  #Split   : 21
% 20.53/9.34  #Chain   : 0
% 20.53/9.34  #Close   : 0
% 20.53/9.34  
% 20.53/9.34  Ordering : KBO
% 20.53/9.34  
% 20.53/9.34  Simplification rules
% 20.53/9.34  ----------------------
% 20.53/9.34  #Subsume      : 3073
% 20.53/9.34  #Demod        : 5832
% 20.53/9.34  #Tautology    : 1077
% 20.53/9.34  #SimpNegUnit  : 61
% 20.53/9.34  #BackRed      : 171
% 20.53/9.34  
% 20.53/9.34  #Partial instantiations: 0
% 20.53/9.34  #Strategies tried      : 1
% 20.53/9.34  
% 20.53/9.34  Timing (in seconds)
% 20.53/9.34  ----------------------
% 20.53/9.34  Preprocessing        : 0.34
% 20.53/9.34  Parsing              : 0.18
% 20.53/9.34  CNF conversion       : 0.03
% 20.53/9.34  Main loop            : 8.22
% 20.53/9.34  Inferencing          : 1.64
% 20.53/9.34  Reduction            : 2.58
% 20.53/9.34  Demodulation         : 1.59
% 20.53/9.34  BG Simplification    : 0.20
% 20.53/9.34  Subsumption          : 3.15
% 20.53/9.34  Abstraction          : 0.28
% 20.53/9.34  MUC search           : 0.00
% 20.53/9.34  Cooper               : 0.00
% 20.53/9.34  Total                : 8.61
% 20.53/9.34  Index Insertion      : 0.00
% 20.53/9.34  Index Deletion       : 0.00
% 20.53/9.34  Index Matching       : 0.00
% 20.53/9.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
