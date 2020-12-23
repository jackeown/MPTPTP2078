%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:40 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 157 expanded)
%              Number of leaves         :   21 (  60 expanded)
%              Depth                    :    9
%              Number of atoms          :  137 ( 475 expanded)
%              Number of equality atoms :    2 (   6 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_84,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ! [C] :
                ( r1_tarski(C,k1_relat_1(k5_relat_1(A,B)))
              <=> ( r1_tarski(C,k1_relat_1(A))
                  & r1_tarski(k9_relat_1(A,C),k1_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_16,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_32,plain,
    ( r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_34,plain,(
    r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_6,plain,(
    ! [A_7,B_9] :
      ( k10_relat_1(A_7,k1_relat_1(B_9)) = k1_relat_1(k5_relat_1(A_7,B_9))
      | ~ v1_relat_1(B_9)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_18,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_4,plain,(
    ! [C_6,A_4,B_5] :
      ( r1_tarski(k9_relat_1(C_6,A_4),k9_relat_1(C_6,B_5))
      | ~ r1_tarski(A_4,B_5)
      | ~ v1_relat_1(C_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_42,plain,(
    ! [B_26,A_27] :
      ( r1_tarski(k9_relat_1(B_26,k10_relat_1(B_26,A_27)),A_27)
      | ~ v1_funct_1(B_26)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_154,plain,(
    ! [A_43,A_44,B_45] :
      ( r1_tarski(A_43,A_44)
      | ~ r1_tarski(A_43,k9_relat_1(B_45,k10_relat_1(B_45,A_44)))
      | ~ v1_funct_1(B_45)
      | ~ v1_relat_1(B_45) ) ),
    inference(resolution,[status(thm)],[c_42,c_2])).

tff(c_193,plain,(
    ! [C_49,A_50,A_51] :
      ( r1_tarski(k9_relat_1(C_49,A_50),A_51)
      | ~ v1_funct_1(C_49)
      | ~ r1_tarski(A_50,k10_relat_1(C_49,A_51))
      | ~ v1_relat_1(C_49) ) ),
    inference(resolution,[status(thm)],[c_4,c_154])).

tff(c_26,plain,
    ( r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_85,plain,(
    ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_47,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_28,B_29)),k1_relat_1(A_28))
      | ~ v1_relat_1(B_29)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_86,plain,(
    ! [A_37,A_38,B_39] :
      ( r1_tarski(A_37,k1_relat_1(A_38))
      | ~ r1_tarski(A_37,k1_relat_1(k5_relat_1(A_38,B_39)))
      | ~ v1_relat_1(B_39)
      | ~ v1_relat_1(A_38) ) ),
    inference(resolution,[status(thm)],[c_47,c_2])).

tff(c_100,plain,
    ( r1_tarski('#skF_4',k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_86])).

tff(c_108,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_16,c_100])).

tff(c_110,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_108])).

tff(c_112,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_24,plain,
    ( r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2'))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_121,plain,
    ( r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2'))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_24])).

tff(c_122,plain,(
    ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_121])).

tff(c_206,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ r1_tarski('#skF_4',k10_relat_1('#skF_1',k1_relat_1('#skF_2')))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_193,c_122])).

tff(c_216,plain,(
    ~ r1_tarski('#skF_4',k10_relat_1('#skF_1',k1_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_206])).

tff(c_221,plain,
    ( ~ r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_216])).

tff(c_224,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_16,c_34,c_221])).

tff(c_226,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_22,plain,
    ( ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_228,plain,
    ( ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_22])).

tff(c_229,plain,(
    ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_228])).

tff(c_243,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_229])).

tff(c_244,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_228])).

tff(c_111,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | r1_tarski('#skF_3',k1_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_271,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_111])).

tff(c_225,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_320,plain,(
    ! [A_57,C_58,B_59] :
      ( r1_tarski(A_57,k10_relat_1(C_58,B_59))
      | ~ r1_tarski(k9_relat_1(C_58,A_57),B_59)
      | ~ r1_tarski(A_57,k1_relat_1(C_58))
      | ~ v1_funct_1(C_58)
      | ~ v1_relat_1(C_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_337,plain,
    ( r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2')))
    | ~ r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_225,c_320])).

tff(c_358,plain,(
    r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_271,c_337])).

tff(c_380,plain,
    ( r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_358])).

tff(c_386,plain,(
    r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_16,c_380])).

tff(c_388,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_244,c_386])).

tff(c_390,plain,(
    ~ r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_28,plain,
    ( ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_394,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_389,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_30,plain,
    ( r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2'))
    | r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_421,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_390,c_30])).

tff(c_611,plain,(
    ! [A_98,C_99,B_100] :
      ( r1_tarski(A_98,k10_relat_1(C_99,B_100))
      | ~ r1_tarski(k9_relat_1(C_99,A_98),B_100)
      | ~ r1_tarski(A_98,k1_relat_1(C_99))
      | ~ v1_funct_1(C_99)
      | ~ v1_relat_1(C_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_629,plain,
    ( r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2')))
    | ~ r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_421,c_611])).

tff(c_646,plain,(
    r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_389,c_629])).

tff(c_657,plain,
    ( r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_646])).

tff(c_663,plain,(
    r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_16,c_657])).

tff(c_665,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_394,c_663])).

tff(c_666,plain,(
    r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_668,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_390,c_666])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:02:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.71/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.40  
% 2.71/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.40  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.71/1.40  
% 2.71/1.40  %Foreground sorts:
% 2.71/1.40  
% 2.71/1.40  
% 2.71/1.40  %Background operators:
% 2.71/1.40  
% 2.71/1.40  
% 2.71/1.40  %Foreground operators:
% 2.71/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.71/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.71/1.40  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.71/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.71/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.71/1.40  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.71/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.71/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.71/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.71/1.40  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.71/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.71/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.71/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.71/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.71/1.40  
% 2.71/1.42  tff(f_84, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: (r1_tarski(C, k1_relat_1(k5_relat_1(A, B))) <=> (r1_tarski(C, k1_relat_1(A)) & r1_tarski(k9_relat_1(A, C), k1_relat_1(B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_1)).
% 2.71/1.42  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 2.71/1.42  tff(f_37, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_relat_1)).
% 2.71/1.42  tff(f_57, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 2.71/1.42  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.71/1.42  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_relat_1)).
% 2.71/1.42  tff(f_67, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 2.71/1.42  tff(c_20, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.71/1.42  tff(c_16, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.71/1.42  tff(c_32, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1')) | r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.71/1.42  tff(c_34, plain, (r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_32])).
% 2.71/1.42  tff(c_6, plain, (![A_7, B_9]: (k10_relat_1(A_7, k1_relat_1(B_9))=k1_relat_1(k5_relat_1(A_7, B_9)) | ~v1_relat_1(B_9) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.71/1.42  tff(c_18, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.71/1.42  tff(c_4, plain, (![C_6, A_4, B_5]: (r1_tarski(k9_relat_1(C_6, A_4), k9_relat_1(C_6, B_5)) | ~r1_tarski(A_4, B_5) | ~v1_relat_1(C_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.71/1.42  tff(c_42, plain, (![B_26, A_27]: (r1_tarski(k9_relat_1(B_26, k10_relat_1(B_26, A_27)), A_27) | ~v1_funct_1(B_26) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.71/1.42  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.71/1.42  tff(c_154, plain, (![A_43, A_44, B_45]: (r1_tarski(A_43, A_44) | ~r1_tarski(A_43, k9_relat_1(B_45, k10_relat_1(B_45, A_44))) | ~v1_funct_1(B_45) | ~v1_relat_1(B_45))), inference(resolution, [status(thm)], [c_42, c_2])).
% 2.71/1.42  tff(c_193, plain, (![C_49, A_50, A_51]: (r1_tarski(k9_relat_1(C_49, A_50), A_51) | ~v1_funct_1(C_49) | ~r1_tarski(A_50, k10_relat_1(C_49, A_51)) | ~v1_relat_1(C_49))), inference(resolution, [status(thm)], [c_4, c_154])).
% 2.71/1.42  tff(c_26, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1')) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.71/1.42  tff(c_85, plain, (~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_26])).
% 2.71/1.42  tff(c_47, plain, (![A_28, B_29]: (r1_tarski(k1_relat_1(k5_relat_1(A_28, B_29)), k1_relat_1(A_28)) | ~v1_relat_1(B_29) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.71/1.42  tff(c_86, plain, (![A_37, A_38, B_39]: (r1_tarski(A_37, k1_relat_1(A_38)) | ~r1_tarski(A_37, k1_relat_1(k5_relat_1(A_38, B_39))) | ~v1_relat_1(B_39) | ~v1_relat_1(A_38))), inference(resolution, [status(thm)], [c_47, c_2])).
% 2.71/1.42  tff(c_100, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_34, c_86])).
% 2.71/1.42  tff(c_108, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_16, c_100])).
% 2.71/1.42  tff(c_110, plain, $false, inference(negUnitSimplification, [status(thm)], [c_85, c_108])).
% 2.71/1.42  tff(c_112, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_26])).
% 2.71/1.42  tff(c_24, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2')) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.71/1.42  tff(c_121, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2')) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_24])).
% 2.71/1.42  tff(c_122, plain, (~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_121])).
% 2.71/1.42  tff(c_206, plain, (~v1_funct_1('#skF_1') | ~r1_tarski('#skF_4', k10_relat_1('#skF_1', k1_relat_1('#skF_2'))) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_193, c_122])).
% 2.71/1.42  tff(c_216, plain, (~r1_tarski('#skF_4', k10_relat_1('#skF_1', k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_206])).
% 2.71/1.42  tff(c_221, plain, (~r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6, c_216])).
% 2.71/1.42  tff(c_224, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_16, c_34, c_221])).
% 2.71/1.42  tff(c_226, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_121])).
% 2.71/1.42  tff(c_22, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.71/1.42  tff(c_228, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_22])).
% 2.71/1.42  tff(c_229, plain, (~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_228])).
% 2.71/1.42  tff(c_243, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_226, c_229])).
% 2.71/1.42  tff(c_244, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_228])).
% 2.71/1.42  tff(c_111, plain, (~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | r1_tarski('#skF_3', k1_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_26])).
% 2.71/1.42  tff(c_271, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_226, c_111])).
% 2.71/1.42  tff(c_225, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_121])).
% 2.71/1.42  tff(c_320, plain, (![A_57, C_58, B_59]: (r1_tarski(A_57, k10_relat_1(C_58, B_59)) | ~r1_tarski(k9_relat_1(C_58, A_57), B_59) | ~r1_tarski(A_57, k1_relat_1(C_58)) | ~v1_funct_1(C_58) | ~v1_relat_1(C_58))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.71/1.42  tff(c_337, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2'))) | ~r1_tarski('#skF_3', k1_relat_1('#skF_1')) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_225, c_320])).
% 2.71/1.42  tff(c_358, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_271, c_337])).
% 2.71/1.42  tff(c_380, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6, c_358])).
% 2.71/1.42  tff(c_386, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_16, c_380])).
% 2.71/1.42  tff(c_388, plain, $false, inference(negUnitSimplification, [status(thm)], [c_244, c_386])).
% 2.71/1.42  tff(c_390, plain, (~r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_32])).
% 2.71/1.42  tff(c_28, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.71/1.42  tff(c_394, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_28])).
% 2.71/1.42  tff(c_389, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_32])).
% 2.71/1.42  tff(c_30, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2')) | r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.71/1.42  tff(c_421, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_390, c_30])).
% 2.71/1.42  tff(c_611, plain, (![A_98, C_99, B_100]: (r1_tarski(A_98, k10_relat_1(C_99, B_100)) | ~r1_tarski(k9_relat_1(C_99, A_98), B_100) | ~r1_tarski(A_98, k1_relat_1(C_99)) | ~v1_funct_1(C_99) | ~v1_relat_1(C_99))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.71/1.42  tff(c_629, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2'))) | ~r1_tarski('#skF_3', k1_relat_1('#skF_1')) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_421, c_611])).
% 2.71/1.42  tff(c_646, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_389, c_629])).
% 2.71/1.42  tff(c_657, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6, c_646])).
% 2.71/1.42  tff(c_663, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_16, c_657])).
% 2.71/1.42  tff(c_665, plain, $false, inference(negUnitSimplification, [status(thm)], [c_394, c_663])).
% 2.71/1.42  tff(c_666, plain, (r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_28])).
% 2.71/1.42  tff(c_668, plain, $false, inference(negUnitSimplification, [status(thm)], [c_390, c_666])).
% 2.71/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.42  
% 2.71/1.42  Inference rules
% 2.71/1.42  ----------------------
% 2.71/1.42  #Ref     : 0
% 2.71/1.42  #Sup     : 142
% 2.71/1.42  #Fact    : 0
% 2.71/1.42  #Define  : 0
% 2.71/1.42  #Split   : 6
% 2.71/1.42  #Chain   : 0
% 2.71/1.42  #Close   : 0
% 2.71/1.42  
% 2.71/1.42  Ordering : KBO
% 2.71/1.42  
% 2.71/1.42  Simplification rules
% 2.71/1.42  ----------------------
% 2.71/1.42  #Subsume      : 14
% 2.71/1.42  #Demod        : 56
% 2.71/1.42  #Tautology    : 19
% 2.71/1.42  #SimpNegUnit  : 7
% 2.71/1.42  #BackRed      : 0
% 2.71/1.42  
% 2.71/1.42  #Partial instantiations: 0
% 2.71/1.42  #Strategies tried      : 1
% 2.71/1.42  
% 2.71/1.42  Timing (in seconds)
% 2.71/1.42  ----------------------
% 2.71/1.42  Preprocessing        : 0.31
% 2.71/1.42  Parsing              : 0.16
% 2.71/1.42  CNF conversion       : 0.02
% 2.71/1.42  Main loop            : 0.34
% 2.71/1.42  Inferencing          : 0.12
% 2.71/1.42  Reduction            : 0.09
% 2.71/1.42  Demodulation         : 0.06
% 2.71/1.42  BG Simplification    : 0.02
% 2.71/1.42  Subsumption          : 0.08
% 2.71/1.42  Abstraction          : 0.02
% 2.71/1.42  MUC search           : 0.00
% 2.71/1.42  Cooper               : 0.00
% 2.71/1.42  Total                : 0.68
% 2.71/1.42  Index Insertion      : 0.00
% 2.71/1.42  Index Deletion       : 0.00
% 2.71/1.42  Index Matching       : 0.00
% 2.71/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
