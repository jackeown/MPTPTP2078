%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0460+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:20 EST 2020

% Result     : Theorem 12.67s
% Output     : CNFRefutation 12.78s
% Verified   : 
% Statistics : Number of formulae       :   50 (  99 expanded)
%              Number of leaves         :   23 (  47 expanded)
%              Depth                    :   13
%              Number of atoms          :  112 ( 324 expanded)
%              Number of equality atoms :    1 (   6 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k5_relat_1 > k4_tarski > #nlpp > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_5 > #skF_9 > #skF_7 > #skF_3 > #skF_2 > #skF_8 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( v1_relat_1(C)
               => ( r1_tarski(A,B)
                 => r1_tarski(k5_relat_1(C,A),k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_34,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( C = k5_relat_1(A,B)
              <=> ! [D,E] :
                    ( r2_hidden(k4_tarski(D,E),C)
                  <=> ? [F] :
                        ( r2_hidden(k4_tarski(D,F),A)
                        & r2_hidden(k4_tarski(F,E),B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_34,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_26,plain,(
    ! [A_117,B_118] :
      ( v1_relat_1(k5_relat_1(A_117,B_118))
      | ~ v1_relat_1(B_118)
      | ~ v1_relat_1(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_36,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_6,plain,(
    ! [A_1,B_11] :
      ( r2_hidden(k4_tarski('#skF_1'(A_1,B_11),'#skF_2'(A_1,B_11)),A_1)
      | r1_tarski(A_1,B_11)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_30,plain,(
    r1_tarski('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_24,plain,(
    ! [D_109,B_70,A_18,E_110] :
      ( r2_hidden(k4_tarski(D_109,'#skF_3'(B_70,A_18,k5_relat_1(A_18,B_70),D_109,E_110)),A_18)
      | ~ r2_hidden(k4_tarski(D_109,E_110),k5_relat_1(A_18,B_70))
      | ~ v1_relat_1(k5_relat_1(A_18,B_70))
      | ~ v1_relat_1(B_70)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_147,plain,(
    ! [B_161,A_162,D_163,E_164] :
      ( r2_hidden(k4_tarski('#skF_3'(B_161,A_162,k5_relat_1(A_162,B_161),D_163,E_164),E_164),B_161)
      | ~ r2_hidden(k4_tarski(D_163,E_164),k5_relat_1(A_162,B_161))
      | ~ v1_relat_1(k5_relat_1(A_162,B_161))
      | ~ v1_relat_1(B_161)
      | ~ v1_relat_1(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2,plain,(
    ! [C_16,D_17,B_11,A_1] :
      ( r2_hidden(k4_tarski(C_16,D_17),B_11)
      | ~ r2_hidden(k4_tarski(C_16,D_17),A_1)
      | ~ r1_tarski(A_1,B_11)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_187,plain,(
    ! [B_180,A_181,D_179,B_178,E_182] :
      ( r2_hidden(k4_tarski('#skF_3'(B_178,A_181,k5_relat_1(A_181,B_178),D_179,E_182),E_182),B_180)
      | ~ r1_tarski(B_178,B_180)
      | ~ r2_hidden(k4_tarski(D_179,E_182),k5_relat_1(A_181,B_178))
      | ~ v1_relat_1(k5_relat_1(A_181,B_178))
      | ~ v1_relat_1(B_178)
      | ~ v1_relat_1(A_181) ) ),
    inference(resolution,[status(thm)],[c_147,c_2])).

tff(c_20,plain,(
    ! [B_70,F_113,D_109,E_110,A_18] :
      ( r2_hidden(k4_tarski(D_109,E_110),k5_relat_1(A_18,B_70))
      | ~ r2_hidden(k4_tarski(F_113,E_110),B_70)
      | ~ r2_hidden(k4_tarski(D_109,F_113),A_18)
      | ~ v1_relat_1(k5_relat_1(A_18,B_70))
      | ~ v1_relat_1(B_70)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_8833,plain,(
    ! [B_1053,B_1057,D_1059,E_1056,A_1054,D_1058,A_1055] :
      ( r2_hidden(k4_tarski(D_1059,E_1056),k5_relat_1(A_1054,B_1053))
      | ~ r2_hidden(k4_tarski(D_1059,'#skF_3'(B_1057,A_1055,k5_relat_1(A_1055,B_1057),D_1058,E_1056)),A_1054)
      | ~ v1_relat_1(k5_relat_1(A_1054,B_1053))
      | ~ v1_relat_1(B_1053)
      | ~ v1_relat_1(A_1054)
      | ~ r1_tarski(B_1057,B_1053)
      | ~ r2_hidden(k4_tarski(D_1058,E_1056),k5_relat_1(A_1055,B_1057))
      | ~ v1_relat_1(k5_relat_1(A_1055,B_1057))
      | ~ v1_relat_1(B_1057)
      | ~ v1_relat_1(A_1055) ) ),
    inference(resolution,[status(thm)],[c_187,c_20])).

tff(c_8877,plain,(
    ! [D_1063,B_1062,E_1064,B_1060,A_1061] :
      ( r2_hidden(k4_tarski(D_1063,E_1064),k5_relat_1(A_1061,B_1062))
      | ~ v1_relat_1(k5_relat_1(A_1061,B_1062))
      | ~ v1_relat_1(B_1062)
      | ~ r1_tarski(B_1060,B_1062)
      | ~ r2_hidden(k4_tarski(D_1063,E_1064),k5_relat_1(A_1061,B_1060))
      | ~ v1_relat_1(k5_relat_1(A_1061,B_1060))
      | ~ v1_relat_1(B_1060)
      | ~ v1_relat_1(A_1061) ) ),
    inference(resolution,[status(thm)],[c_24,c_8833])).

tff(c_8893,plain,(
    ! [D_1063,E_1064,A_1061] :
      ( r2_hidden(k4_tarski(D_1063,E_1064),k5_relat_1(A_1061,'#skF_10'))
      | ~ v1_relat_1(k5_relat_1(A_1061,'#skF_10'))
      | ~ v1_relat_1('#skF_10')
      | ~ r2_hidden(k4_tarski(D_1063,E_1064),k5_relat_1(A_1061,'#skF_9'))
      | ~ v1_relat_1(k5_relat_1(A_1061,'#skF_9'))
      | ~ v1_relat_1('#skF_9')
      | ~ v1_relat_1(A_1061) ) ),
    inference(resolution,[status(thm)],[c_30,c_8877])).

tff(c_8906,plain,(
    ! [D_1065,E_1066,A_1067] :
      ( r2_hidden(k4_tarski(D_1065,E_1066),k5_relat_1(A_1067,'#skF_10'))
      | ~ v1_relat_1(k5_relat_1(A_1067,'#skF_10'))
      | ~ r2_hidden(k4_tarski(D_1065,E_1066),k5_relat_1(A_1067,'#skF_9'))
      | ~ v1_relat_1(k5_relat_1(A_1067,'#skF_9'))
      | ~ v1_relat_1(A_1067) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_8893])).

tff(c_4,plain,(
    ! [A_1,B_11] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_1,B_11),'#skF_2'(A_1,B_11)),B_11)
      | r1_tarski(A_1,B_11)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_10845,plain,(
    ! [A_1098,A_1099] :
      ( r1_tarski(A_1098,k5_relat_1(A_1099,'#skF_10'))
      | ~ v1_relat_1(A_1098)
      | ~ v1_relat_1(k5_relat_1(A_1099,'#skF_10'))
      | ~ r2_hidden(k4_tarski('#skF_1'(A_1098,k5_relat_1(A_1099,'#skF_10')),'#skF_2'(A_1098,k5_relat_1(A_1099,'#skF_10'))),k5_relat_1(A_1099,'#skF_9'))
      | ~ v1_relat_1(k5_relat_1(A_1099,'#skF_9'))
      | ~ v1_relat_1(A_1099) ) ),
    inference(resolution,[status(thm)],[c_8906,c_4])).

tff(c_10989,plain,(
    ! [A_1100] :
      ( ~ v1_relat_1(k5_relat_1(A_1100,'#skF_10'))
      | ~ v1_relat_1(A_1100)
      | r1_tarski(k5_relat_1(A_1100,'#skF_9'),k5_relat_1(A_1100,'#skF_10'))
      | ~ v1_relat_1(k5_relat_1(A_1100,'#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_6,c_10845])).

tff(c_28,plain,(
    ~ r1_tarski(k5_relat_1('#skF_11','#skF_9'),k5_relat_1('#skF_11','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_11121,plain,
    ( ~ v1_relat_1(k5_relat_1('#skF_11','#skF_10'))
    | ~ v1_relat_1('#skF_11')
    | ~ v1_relat_1(k5_relat_1('#skF_11','#skF_9')) ),
    inference(resolution,[status(thm)],[c_10989,c_28])).

tff(c_11218,plain,
    ( ~ v1_relat_1(k5_relat_1('#skF_11','#skF_10'))
    | ~ v1_relat_1(k5_relat_1('#skF_11','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_11121])).

tff(c_11219,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_11','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_11218])).

tff(c_11222,plain,
    ( ~ v1_relat_1('#skF_9')
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_26,c_11219])).

tff(c_11226,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_36,c_11222])).

tff(c_11227,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_11','#skF_10')) ),
    inference(splitRight,[status(thm)],[c_11218])).

tff(c_11231,plain,
    ( ~ v1_relat_1('#skF_10')
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_26,c_11227])).

tff(c_11235,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34,c_11231])).

%------------------------------------------------------------------------------
