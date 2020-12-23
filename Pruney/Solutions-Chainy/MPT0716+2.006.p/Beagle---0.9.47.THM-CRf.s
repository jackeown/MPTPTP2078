%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:37 EST 2020

% Result     : Theorem 11.57s
% Output     : CNFRefutation 11.57s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 448 expanded)
%              Number of leaves         :   24 ( 162 expanded)
%              Depth                    :   23
%              Number of atoms          :  231 (1212 expanded)
%              Number of equality atoms :   21 ( 103 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_97,negated_conjecture,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ! [D] :
          ( v1_relat_1(D)
         => ( ( r1_tarski(C,D)
              & r1_tarski(A,B) )
           => r1_tarski(k9_relat_1(C,A),k9_relat_1(D,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_relat_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_43,plain,(
    ! [A_29,B_30] :
      ( k2_xboole_0(A_29,B_30) = B_30
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_47,plain,(
    ! [B_2] : k2_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_43])).

tff(c_26,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_24,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_16,plain,(
    ! [A_16,B_18] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_16,B_18)),k1_relat_1(A_16))
      | ~ v1_relat_1(B_18)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_40,plain,
    ( r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_73,plain,(
    r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_97,plain,(
    k2_xboole_0('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) = k1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_73,c_10])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(k2_xboole_0(A_3,B_4),C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_260,plain,(
    ! [C_53] :
      ( r1_tarski('#skF_4',C_53)
      | ~ r1_tarski(k1_relat_1(k5_relat_1('#skF_1','#skF_2')),C_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_8])).

tff(c_268,plain,
    ( r1_tarski('#skF_4',k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_260])).

tff(c_284,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_268])).

tff(c_296,plain,(
    k2_xboole_0('#skF_4',k1_relat_1('#skF_1')) = k1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_284,c_10])).

tff(c_167,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_46,B_47)),k1_relat_1(A_46))
      | ~ v1_relat_1(B_47)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_174,plain,(
    ! [A_46,B_47] :
      ( k2_xboole_0(k1_relat_1(k5_relat_1(A_46,B_47)),k1_relat_1(A_46)) = k1_relat_1(A_46)
      | ~ v1_relat_1(B_47)
      | ~ v1_relat_1(A_46) ) ),
    inference(resolution,[status(thm)],[c_167,c_10])).

tff(c_64,plain,(
    ! [A_34,C_35,B_36] :
      ( r1_tarski(A_34,C_35)
      | ~ r1_tarski(k2_xboole_0(A_34,B_36),C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_74,plain,(
    ! [A_37,B_38] : r1_tarski(A_37,k2_xboole_0(A_37,B_38)) ),
    inference(resolution,[status(thm)],[c_6,c_64])).

tff(c_98,plain,(
    ! [A_39,B_40,B_41] : r1_tarski(A_39,k2_xboole_0(k2_xboole_0(A_39,B_40),B_41)) ),
    inference(resolution,[status(thm)],[c_74,c_8])).

tff(c_682,plain,(
    ! [A_78,B_79,B_80] : k2_xboole_0(A_78,k2_xboole_0(k2_xboole_0(A_78,B_79),B_80)) = k2_xboole_0(k2_xboole_0(A_78,B_79),B_80) ),
    inference(resolution,[status(thm)],[c_98,c_10])).

tff(c_807,plain,(
    ! [B_80] : k2_xboole_0(k2_xboole_0('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))),B_80) = k2_xboole_0('#skF_4',k2_xboole_0(k1_relat_1(k5_relat_1('#skF_1','#skF_2')),B_80)) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_682])).

tff(c_1897,plain,(
    ! [B_149] : k2_xboole_0('#skF_4',k2_xboole_0(k1_relat_1(k5_relat_1('#skF_1','#skF_2')),B_149)) = k2_xboole_0(k1_relat_1(k5_relat_1('#skF_1','#skF_2')),B_149) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_807])).

tff(c_1946,plain,
    ( k2_xboole_0(k1_relat_1(k5_relat_1('#skF_1','#skF_2')),k1_relat_1('#skF_1')) = k2_xboole_0('#skF_4',k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_1897])).

tff(c_1970,plain,(
    k2_xboole_0(k1_relat_1(k5_relat_1('#skF_1','#skF_2')),k1_relat_1('#skF_1')) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_296,c_1946])).

tff(c_72,plain,(
    ! [A_34,B_36] : r1_tarski(A_34,k2_xboole_0(A_34,B_36)) ),
    inference(resolution,[status(thm)],[c_6,c_64])).

tff(c_2050,plain,(
    r1_tarski(k1_relat_1(k5_relat_1('#skF_1','#skF_2')),k1_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1970,c_72])).

tff(c_14,plain,(
    ! [A_13,B_15] :
      ( k10_relat_1(A_13,k1_relat_1(B_15)) = k1_relat_1(k5_relat_1(A_13,B_15))
      | ~ v1_relat_1(B_15)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_469,plain,(
    ! [A_65,B_66] :
      ( k10_relat_1(A_65,k1_relat_1(B_66)) = k1_relat_1(k5_relat_1(A_65,B_66))
      | ~ v1_relat_1(B_66)
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_18,plain,(
    ! [B_20,A_19] :
      ( r1_tarski(k9_relat_1(B_20,k10_relat_1(B_20,A_19)),A_19)
      | ~ v1_funct_1(B_20)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2340,plain,(
    ! [A_159,B_160] :
      ( r1_tarski(k9_relat_1(A_159,k1_relat_1(k5_relat_1(A_159,B_160))),k1_relat_1(B_160))
      | ~ v1_funct_1(A_159)
      | ~ v1_relat_1(A_159)
      | ~ v1_relat_1(B_160)
      | ~ v1_relat_1(A_159) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_469,c_18])).

tff(c_20,plain,(
    ! [A_21,C_23,B_22] :
      ( r1_tarski(A_21,k10_relat_1(C_23,B_22))
      | ~ r1_tarski(k9_relat_1(C_23,A_21),B_22)
      | ~ r1_tarski(A_21,k1_relat_1(C_23))
      | ~ v1_funct_1(C_23)
      | ~ v1_relat_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_7100,plain,(
    ! [A_305,B_306] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_305,B_306)),k10_relat_1(A_305,k1_relat_1(B_306)))
      | ~ r1_tarski(k1_relat_1(k5_relat_1(A_305,B_306)),k1_relat_1(A_305))
      | ~ v1_funct_1(A_305)
      | ~ v1_relat_1(B_306)
      | ~ v1_relat_1(A_305) ) ),
    inference(resolution,[status(thm)],[c_2340,c_20])).

tff(c_234,plain,(
    ! [C_5] :
      ( r1_tarski('#skF_4',C_5)
      | ~ r1_tarski(k1_relat_1(k5_relat_1('#skF_1','#skF_2')),C_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_8])).

tff(c_7110,plain,
    ( r1_tarski('#skF_4',k10_relat_1('#skF_1',k1_relat_1('#skF_2')))
    | ~ r1_tarski(k1_relat_1(k5_relat_1('#skF_1','#skF_2')),k1_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_7100,c_234])).

tff(c_7124,plain,(
    r1_tarski('#skF_4',k10_relat_1('#skF_1',k1_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_26,c_2050,c_7110])).

tff(c_7147,plain,(
    k2_xboole_0('#skF_4',k10_relat_1('#skF_1',k1_relat_1('#skF_2'))) = k10_relat_1('#skF_1',k1_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_7124,c_10])).

tff(c_7229,plain,
    ( k2_xboole_0('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) = k10_relat_1('#skF_1',k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_7147])).

tff(c_7239,plain,(
    k10_relat_1('#skF_1',k1_relat_1('#skF_2')) = k1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_97,c_7229])).

tff(c_341,plain,(
    ! [B_55,A_56] :
      ( r1_tarski(k9_relat_1(B_55,k10_relat_1(B_55,A_56)),A_56)
      | ~ v1_funct_1(B_55)
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_648,plain,(
    ! [B_76,A_77] :
      ( k2_xboole_0(k9_relat_1(B_76,k10_relat_1(B_76,A_77)),A_77) = A_77
      | ~ v1_funct_1(B_76)
      | ~ v1_relat_1(B_76) ) ),
    inference(resolution,[status(thm)],[c_341,c_10])).

tff(c_87,plain,(
    ! [A_3,B_4,B_38] : r1_tarski(A_3,k2_xboole_0(k2_xboole_0(A_3,B_4),B_38)) ),
    inference(resolution,[status(thm)],[c_74,c_8])).

tff(c_666,plain,(
    ! [B_76,A_77,B_38] :
      ( r1_tarski(k9_relat_1(B_76,k10_relat_1(B_76,A_77)),k2_xboole_0(A_77,B_38))
      | ~ v1_funct_1(B_76)
      | ~ v1_relat_1(B_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_648,c_87])).

tff(c_7442,plain,(
    ! [B_38] :
      ( r1_tarski(k9_relat_1('#skF_1',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))),k2_xboole_0(k1_relat_1('#skF_2'),B_38))
      | ~ v1_funct_1('#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7239,c_666])).

tff(c_7657,plain,(
    ! [B_317] : r1_tarski(k9_relat_1('#skF_1',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))),k2_xboole_0(k1_relat_1('#skF_2'),B_317)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_7442])).

tff(c_7668,plain,(
    ! [B_317] :
      ( r1_tarski(k1_relat_1(k5_relat_1('#skF_1','#skF_2')),k10_relat_1('#skF_1',k2_xboole_0(k1_relat_1('#skF_2'),B_317)))
      | ~ r1_tarski(k1_relat_1(k5_relat_1('#skF_1','#skF_2')),k1_relat_1('#skF_1'))
      | ~ v1_funct_1('#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_7657,c_20])).

tff(c_7705,plain,(
    ! [B_318] : r1_tarski(k1_relat_1(k5_relat_1('#skF_1','#skF_2')),k10_relat_1('#skF_1',k2_xboole_0(k1_relat_1('#skF_2'),B_318))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_2050,c_7668])).

tff(c_7740,plain,(
    ! [B_318] : r1_tarski('#skF_4',k10_relat_1('#skF_1',k2_xboole_0(k1_relat_1('#skF_2'),B_318))) ),
    inference(resolution,[status(thm)],[c_7705,c_234])).

tff(c_1055,plain,(
    ! [C_93,A_94,D_95,B_96] :
      ( r1_tarski(k9_relat_1(C_93,A_94),k9_relat_1(D_95,B_96))
      | ~ r1_tarski(A_94,B_96)
      | ~ r1_tarski(C_93,D_95)
      | ~ v1_relat_1(D_95)
      | ~ v1_relat_1(C_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2754,plain,(
    ! [C_176,A_177,D_178,B_179] :
      ( k2_xboole_0(k9_relat_1(C_176,A_177),k9_relat_1(D_178,B_179)) = k9_relat_1(D_178,B_179)
      | ~ r1_tarski(A_177,B_179)
      | ~ r1_tarski(C_176,D_178)
      | ~ v1_relat_1(D_178)
      | ~ v1_relat_1(C_176) ) ),
    inference(resolution,[status(thm)],[c_1055,c_10])).

tff(c_5659,plain,(
    ! [A_260,D_259,C_261,B_258,C_262] :
      ( r1_tarski(k9_relat_1(C_261,A_260),C_262)
      | ~ r1_tarski(k9_relat_1(D_259,B_258),C_262)
      | ~ r1_tarski(A_260,B_258)
      | ~ r1_tarski(C_261,D_259)
      | ~ v1_relat_1(D_259)
      | ~ v1_relat_1(C_261) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2754,c_8])).

tff(c_17137,plain,(
    ! [C_525,A_526,A_527,B_528] :
      ( r1_tarski(k9_relat_1(C_525,A_526),A_527)
      | ~ r1_tarski(A_526,k10_relat_1(B_528,A_527))
      | ~ r1_tarski(C_525,B_528)
      | ~ v1_relat_1(C_525)
      | ~ v1_funct_1(B_528)
      | ~ v1_relat_1(B_528) ) ),
    inference(resolution,[status(thm)],[c_18,c_5659])).

tff(c_17171,plain,(
    ! [C_525,B_318] :
      ( r1_tarski(k9_relat_1(C_525,'#skF_4'),k2_xboole_0(k1_relat_1('#skF_2'),B_318))
      | ~ r1_tarski(C_525,'#skF_1')
      | ~ v1_relat_1(C_525)
      | ~ v1_funct_1('#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_7740,c_17137])).

tff(c_17260,plain,(
    ! [C_529,B_530] :
      ( r1_tarski(k9_relat_1(C_529,'#skF_4'),k2_xboole_0(k1_relat_1('#skF_2'),B_530))
      | ~ r1_tarski(C_529,'#skF_1')
      | ~ v1_relat_1(C_529) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_17171])).

tff(c_17315,plain,(
    ! [C_531] :
      ( r1_tarski(k9_relat_1(C_531,'#skF_4'),k1_relat_1('#skF_2'))
      | ~ r1_tarski(C_531,'#skF_1')
      | ~ v1_relat_1(C_531) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_17260])).

tff(c_34,plain,
    ( r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_557,plain,
    ( r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_34])).

tff(c_558,plain,(
    ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_557])).

tff(c_17333,plain,
    ( ~ r1_tarski('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_17315,c_558])).

tff(c_17350,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_6,c_17333])).

tff(c_17352,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_557])).

tff(c_30,plain,
    ( ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_17361,plain,
    ( ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_30])).

tff(c_17362,plain,(
    ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_17361])).

tff(c_17371,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17352,c_17362])).

tff(c_17372,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_17361])).

tff(c_17351,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_557])).

tff(c_17373,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_17361])).

tff(c_32,plain,
    ( r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2'))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_17382,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_17373,c_32])).

tff(c_17598,plain,(
    ! [A_544,C_545,B_546] :
      ( r1_tarski(A_544,k10_relat_1(C_545,B_546))
      | ~ r1_tarski(k9_relat_1(C_545,A_544),B_546)
      | ~ r1_tarski(A_544,k1_relat_1(C_545))
      | ~ v1_funct_1(C_545)
      | ~ v1_relat_1(C_545) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_17616,plain,
    ( r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2')))
    | ~ r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_17382,c_17598])).

tff(c_17654,plain,(
    r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_17351,c_17616])).

tff(c_17671,plain,
    ( r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_17654])).

tff(c_17675,plain,(
    r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_17671])).

tff(c_17677,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17372,c_17675])).

tff(c_17679,plain,(
    ~ r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_36,plain,
    ( ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_17735,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_17679,c_36])).

tff(c_17678,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_38,plain,
    ( r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2'))
    | r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_17704,plain,(
    r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_17705,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17679,c_17704])).

tff(c_17706,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_18871,plain,(
    ! [A_618,C_619,B_620] :
      ( r1_tarski(A_618,k10_relat_1(C_619,B_620))
      | ~ r1_tarski(k9_relat_1(C_619,A_618),B_620)
      | ~ r1_tarski(A_618,k1_relat_1(C_619))
      | ~ v1_funct_1(C_619)
      | ~ v1_relat_1(C_619) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_18904,plain,
    ( r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2')))
    | ~ r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_17706,c_18871])).

tff(c_18933,plain,(
    r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_17678,c_18904])).

tff(c_18943,plain,
    ( r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_18933])).

tff(c_18947,plain,(
    r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_18943])).

tff(c_18949,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17735,c_18947])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:54:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.57/4.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.57/4.33  
% 11.57/4.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.57/4.34  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 11.57/4.34  
% 11.57/4.34  %Foreground sorts:
% 11.57/4.34  
% 11.57/4.34  
% 11.57/4.34  %Background operators:
% 11.57/4.34  
% 11.57/4.34  
% 11.57/4.34  %Foreground operators:
% 11.57/4.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.57/4.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.57/4.34  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 11.57/4.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.57/4.34  tff('#skF_2', type, '#skF_2': $i).
% 11.57/4.34  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 11.57/4.34  tff('#skF_3', type, '#skF_3': $i).
% 11.57/4.34  tff('#skF_1', type, '#skF_1': $i).
% 11.57/4.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.57/4.34  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 11.57/4.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.57/4.34  tff('#skF_4', type, '#skF_4': $i).
% 11.57/4.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.57/4.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.57/4.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.57/4.34  
% 11.57/4.36  tff(f_97, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: (r1_tarski(C, k1_relat_1(k5_relat_1(A, B))) <=> (r1_tarski(C, k1_relat_1(A)) & r1_tarski(k9_relat_1(A, C), k1_relat_1(B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_1)).
% 11.57/4.36  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.57/4.36  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 11.57/4.36  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_relat_1)).
% 11.57/4.36  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 11.57/4.36  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 11.57/4.36  tff(f_70, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 11.57/4.36  tff(f_80, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 11.57/4.36  tff(f_50, axiom, (![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k9_relat_1(C, A), k9_relat_1(D, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_relat_1)).
% 11.57/4.36  tff(c_28, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.57/4.36  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.57/4.36  tff(c_43, plain, (![A_29, B_30]: (k2_xboole_0(A_29, B_30)=B_30 | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.57/4.36  tff(c_47, plain, (![B_2]: (k2_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_43])).
% 11.57/4.36  tff(c_26, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.57/4.36  tff(c_24, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.57/4.36  tff(c_16, plain, (![A_16, B_18]: (r1_tarski(k1_relat_1(k5_relat_1(A_16, B_18)), k1_relat_1(A_16)) | ~v1_relat_1(B_18) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.57/4.36  tff(c_40, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1')) | r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.57/4.36  tff(c_73, plain, (r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_40])).
% 11.57/4.36  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.57/4.36  tff(c_97, plain, (k2_xboole_0('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))=k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_73, c_10])).
% 11.57/4.36  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(k2_xboole_0(A_3, B_4), C_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.57/4.36  tff(c_260, plain, (![C_53]: (r1_tarski('#skF_4', C_53) | ~r1_tarski(k1_relat_1(k5_relat_1('#skF_1', '#skF_2')), C_53))), inference(superposition, [status(thm), theory('equality')], [c_97, c_8])).
% 11.57/4.36  tff(c_268, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_16, c_260])).
% 11.57/4.36  tff(c_284, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_268])).
% 11.57/4.36  tff(c_296, plain, (k2_xboole_0('#skF_4', k1_relat_1('#skF_1'))=k1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_284, c_10])).
% 11.57/4.36  tff(c_167, plain, (![A_46, B_47]: (r1_tarski(k1_relat_1(k5_relat_1(A_46, B_47)), k1_relat_1(A_46)) | ~v1_relat_1(B_47) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.57/4.36  tff(c_174, plain, (![A_46, B_47]: (k2_xboole_0(k1_relat_1(k5_relat_1(A_46, B_47)), k1_relat_1(A_46))=k1_relat_1(A_46) | ~v1_relat_1(B_47) | ~v1_relat_1(A_46))), inference(resolution, [status(thm)], [c_167, c_10])).
% 11.57/4.36  tff(c_64, plain, (![A_34, C_35, B_36]: (r1_tarski(A_34, C_35) | ~r1_tarski(k2_xboole_0(A_34, B_36), C_35))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.57/4.36  tff(c_74, plain, (![A_37, B_38]: (r1_tarski(A_37, k2_xboole_0(A_37, B_38)))), inference(resolution, [status(thm)], [c_6, c_64])).
% 11.57/4.36  tff(c_98, plain, (![A_39, B_40, B_41]: (r1_tarski(A_39, k2_xboole_0(k2_xboole_0(A_39, B_40), B_41)))), inference(resolution, [status(thm)], [c_74, c_8])).
% 11.57/4.36  tff(c_682, plain, (![A_78, B_79, B_80]: (k2_xboole_0(A_78, k2_xboole_0(k2_xboole_0(A_78, B_79), B_80))=k2_xboole_0(k2_xboole_0(A_78, B_79), B_80))), inference(resolution, [status(thm)], [c_98, c_10])).
% 11.57/4.36  tff(c_807, plain, (![B_80]: (k2_xboole_0(k2_xboole_0('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), B_80)=k2_xboole_0('#skF_4', k2_xboole_0(k1_relat_1(k5_relat_1('#skF_1', '#skF_2')), B_80)))), inference(superposition, [status(thm), theory('equality')], [c_97, c_682])).
% 11.57/4.36  tff(c_1897, plain, (![B_149]: (k2_xboole_0('#skF_4', k2_xboole_0(k1_relat_1(k5_relat_1('#skF_1', '#skF_2')), B_149))=k2_xboole_0(k1_relat_1(k5_relat_1('#skF_1', '#skF_2')), B_149))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_807])).
% 11.57/4.36  tff(c_1946, plain, (k2_xboole_0(k1_relat_1(k5_relat_1('#skF_1', '#skF_2')), k1_relat_1('#skF_1'))=k2_xboole_0('#skF_4', k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_174, c_1897])).
% 11.57/4.36  tff(c_1970, plain, (k2_xboole_0(k1_relat_1(k5_relat_1('#skF_1', '#skF_2')), k1_relat_1('#skF_1'))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_296, c_1946])).
% 11.57/4.36  tff(c_72, plain, (![A_34, B_36]: (r1_tarski(A_34, k2_xboole_0(A_34, B_36)))), inference(resolution, [status(thm)], [c_6, c_64])).
% 11.57/4.36  tff(c_2050, plain, (r1_tarski(k1_relat_1(k5_relat_1('#skF_1', '#skF_2')), k1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1970, c_72])).
% 11.57/4.36  tff(c_14, plain, (![A_13, B_15]: (k10_relat_1(A_13, k1_relat_1(B_15))=k1_relat_1(k5_relat_1(A_13, B_15)) | ~v1_relat_1(B_15) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.57/4.36  tff(c_469, plain, (![A_65, B_66]: (k10_relat_1(A_65, k1_relat_1(B_66))=k1_relat_1(k5_relat_1(A_65, B_66)) | ~v1_relat_1(B_66) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.57/4.36  tff(c_18, plain, (![B_20, A_19]: (r1_tarski(k9_relat_1(B_20, k10_relat_1(B_20, A_19)), A_19) | ~v1_funct_1(B_20) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_70])).
% 11.57/4.36  tff(c_2340, plain, (![A_159, B_160]: (r1_tarski(k9_relat_1(A_159, k1_relat_1(k5_relat_1(A_159, B_160))), k1_relat_1(B_160)) | ~v1_funct_1(A_159) | ~v1_relat_1(A_159) | ~v1_relat_1(B_160) | ~v1_relat_1(A_159))), inference(superposition, [status(thm), theory('equality')], [c_469, c_18])).
% 11.57/4.36  tff(c_20, plain, (![A_21, C_23, B_22]: (r1_tarski(A_21, k10_relat_1(C_23, B_22)) | ~r1_tarski(k9_relat_1(C_23, A_21), B_22) | ~r1_tarski(A_21, k1_relat_1(C_23)) | ~v1_funct_1(C_23) | ~v1_relat_1(C_23))), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.57/4.36  tff(c_7100, plain, (![A_305, B_306]: (r1_tarski(k1_relat_1(k5_relat_1(A_305, B_306)), k10_relat_1(A_305, k1_relat_1(B_306))) | ~r1_tarski(k1_relat_1(k5_relat_1(A_305, B_306)), k1_relat_1(A_305)) | ~v1_funct_1(A_305) | ~v1_relat_1(B_306) | ~v1_relat_1(A_305))), inference(resolution, [status(thm)], [c_2340, c_20])).
% 11.57/4.36  tff(c_234, plain, (![C_5]: (r1_tarski('#skF_4', C_5) | ~r1_tarski(k1_relat_1(k5_relat_1('#skF_1', '#skF_2')), C_5))), inference(superposition, [status(thm), theory('equality')], [c_97, c_8])).
% 11.57/4.36  tff(c_7110, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_1', k1_relat_1('#skF_2'))) | ~r1_tarski(k1_relat_1(k5_relat_1('#skF_1', '#skF_2')), k1_relat_1('#skF_1')) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_7100, c_234])).
% 11.57/4.36  tff(c_7124, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_1', k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_26, c_2050, c_7110])).
% 11.57/4.36  tff(c_7147, plain, (k2_xboole_0('#skF_4', k10_relat_1('#skF_1', k1_relat_1('#skF_2')))=k10_relat_1('#skF_1', k1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_7124, c_10])).
% 11.57/4.36  tff(c_7229, plain, (k2_xboole_0('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))=k10_relat_1('#skF_1', k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_14, c_7147])).
% 11.57/4.36  tff(c_7239, plain, (k10_relat_1('#skF_1', k1_relat_1('#skF_2'))=k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_97, c_7229])).
% 11.57/4.36  tff(c_341, plain, (![B_55, A_56]: (r1_tarski(k9_relat_1(B_55, k10_relat_1(B_55, A_56)), A_56) | ~v1_funct_1(B_55) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_70])).
% 11.57/4.36  tff(c_648, plain, (![B_76, A_77]: (k2_xboole_0(k9_relat_1(B_76, k10_relat_1(B_76, A_77)), A_77)=A_77 | ~v1_funct_1(B_76) | ~v1_relat_1(B_76))), inference(resolution, [status(thm)], [c_341, c_10])).
% 11.57/4.36  tff(c_87, plain, (![A_3, B_4, B_38]: (r1_tarski(A_3, k2_xboole_0(k2_xboole_0(A_3, B_4), B_38)))), inference(resolution, [status(thm)], [c_74, c_8])).
% 11.57/4.36  tff(c_666, plain, (![B_76, A_77, B_38]: (r1_tarski(k9_relat_1(B_76, k10_relat_1(B_76, A_77)), k2_xboole_0(A_77, B_38)) | ~v1_funct_1(B_76) | ~v1_relat_1(B_76))), inference(superposition, [status(thm), theory('equality')], [c_648, c_87])).
% 11.57/4.36  tff(c_7442, plain, (![B_38]: (r1_tarski(k9_relat_1('#skF_1', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), k2_xboole_0(k1_relat_1('#skF_2'), B_38)) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_7239, c_666])).
% 11.57/4.36  tff(c_7657, plain, (![B_317]: (r1_tarski(k9_relat_1('#skF_1', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), k2_xboole_0(k1_relat_1('#skF_2'), B_317)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_7442])).
% 11.57/4.36  tff(c_7668, plain, (![B_317]: (r1_tarski(k1_relat_1(k5_relat_1('#skF_1', '#skF_2')), k10_relat_1('#skF_1', k2_xboole_0(k1_relat_1('#skF_2'), B_317))) | ~r1_tarski(k1_relat_1(k5_relat_1('#skF_1', '#skF_2')), k1_relat_1('#skF_1')) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_7657, c_20])).
% 11.57/4.36  tff(c_7705, plain, (![B_318]: (r1_tarski(k1_relat_1(k5_relat_1('#skF_1', '#skF_2')), k10_relat_1('#skF_1', k2_xboole_0(k1_relat_1('#skF_2'), B_318))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_2050, c_7668])).
% 11.57/4.36  tff(c_7740, plain, (![B_318]: (r1_tarski('#skF_4', k10_relat_1('#skF_1', k2_xboole_0(k1_relat_1('#skF_2'), B_318))))), inference(resolution, [status(thm)], [c_7705, c_234])).
% 11.57/4.36  tff(c_1055, plain, (![C_93, A_94, D_95, B_96]: (r1_tarski(k9_relat_1(C_93, A_94), k9_relat_1(D_95, B_96)) | ~r1_tarski(A_94, B_96) | ~r1_tarski(C_93, D_95) | ~v1_relat_1(D_95) | ~v1_relat_1(C_93))), inference(cnfTransformation, [status(thm)], [f_50])).
% 11.57/4.36  tff(c_2754, plain, (![C_176, A_177, D_178, B_179]: (k2_xboole_0(k9_relat_1(C_176, A_177), k9_relat_1(D_178, B_179))=k9_relat_1(D_178, B_179) | ~r1_tarski(A_177, B_179) | ~r1_tarski(C_176, D_178) | ~v1_relat_1(D_178) | ~v1_relat_1(C_176))), inference(resolution, [status(thm)], [c_1055, c_10])).
% 11.57/4.36  tff(c_5659, plain, (![A_260, D_259, C_261, B_258, C_262]: (r1_tarski(k9_relat_1(C_261, A_260), C_262) | ~r1_tarski(k9_relat_1(D_259, B_258), C_262) | ~r1_tarski(A_260, B_258) | ~r1_tarski(C_261, D_259) | ~v1_relat_1(D_259) | ~v1_relat_1(C_261))), inference(superposition, [status(thm), theory('equality')], [c_2754, c_8])).
% 11.57/4.36  tff(c_17137, plain, (![C_525, A_526, A_527, B_528]: (r1_tarski(k9_relat_1(C_525, A_526), A_527) | ~r1_tarski(A_526, k10_relat_1(B_528, A_527)) | ~r1_tarski(C_525, B_528) | ~v1_relat_1(C_525) | ~v1_funct_1(B_528) | ~v1_relat_1(B_528))), inference(resolution, [status(thm)], [c_18, c_5659])).
% 11.57/4.36  tff(c_17171, plain, (![C_525, B_318]: (r1_tarski(k9_relat_1(C_525, '#skF_4'), k2_xboole_0(k1_relat_1('#skF_2'), B_318)) | ~r1_tarski(C_525, '#skF_1') | ~v1_relat_1(C_525) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_7740, c_17137])).
% 11.57/4.36  tff(c_17260, plain, (![C_529, B_530]: (r1_tarski(k9_relat_1(C_529, '#skF_4'), k2_xboole_0(k1_relat_1('#skF_2'), B_530)) | ~r1_tarski(C_529, '#skF_1') | ~v1_relat_1(C_529))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_17171])).
% 11.57/4.36  tff(c_17315, plain, (![C_531]: (r1_tarski(k9_relat_1(C_531, '#skF_4'), k1_relat_1('#skF_2')) | ~r1_tarski(C_531, '#skF_1') | ~v1_relat_1(C_531))), inference(superposition, [status(thm), theory('equality')], [c_47, c_17260])).
% 11.57/4.36  tff(c_34, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1')) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.57/4.36  tff(c_557, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1')) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_284, c_34])).
% 11.57/4.36  tff(c_558, plain, (~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_557])).
% 11.57/4.36  tff(c_17333, plain, (~r1_tarski('#skF_1', '#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_17315, c_558])).
% 11.57/4.36  tff(c_17350, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_6, c_17333])).
% 11.57/4.36  tff(c_17352, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_557])).
% 11.57/4.36  tff(c_30, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.57/4.36  tff(c_17361, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_284, c_30])).
% 11.57/4.36  tff(c_17362, plain, (~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_17361])).
% 11.57/4.36  tff(c_17371, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17352, c_17362])).
% 11.57/4.36  tff(c_17372, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_17361])).
% 11.57/4.36  tff(c_17351, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_557])).
% 11.57/4.36  tff(c_17373, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_17361])).
% 11.57/4.36  tff(c_32, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2')) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.57/4.36  tff(c_17382, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_284, c_17373, c_32])).
% 11.57/4.36  tff(c_17598, plain, (![A_544, C_545, B_546]: (r1_tarski(A_544, k10_relat_1(C_545, B_546)) | ~r1_tarski(k9_relat_1(C_545, A_544), B_546) | ~r1_tarski(A_544, k1_relat_1(C_545)) | ~v1_funct_1(C_545) | ~v1_relat_1(C_545))), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.57/4.36  tff(c_17616, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2'))) | ~r1_tarski('#skF_3', k1_relat_1('#skF_1')) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_17382, c_17598])).
% 11.57/4.36  tff(c_17654, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_17351, c_17616])).
% 11.57/4.36  tff(c_17671, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_14, c_17654])).
% 11.57/4.36  tff(c_17675, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_17671])).
% 11.57/4.36  tff(c_17677, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17372, c_17675])).
% 11.57/4.36  tff(c_17679, plain, (~r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_40])).
% 11.57/4.36  tff(c_36, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.57/4.36  tff(c_17735, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_17679, c_36])).
% 11.57/4.36  tff(c_17678, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_40])).
% 11.57/4.36  tff(c_38, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2')) | r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.57/4.36  tff(c_17704, plain, (r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_38])).
% 11.57/4.36  tff(c_17705, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17679, c_17704])).
% 11.57/4.36  tff(c_17706, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_38])).
% 11.57/4.36  tff(c_18871, plain, (![A_618, C_619, B_620]: (r1_tarski(A_618, k10_relat_1(C_619, B_620)) | ~r1_tarski(k9_relat_1(C_619, A_618), B_620) | ~r1_tarski(A_618, k1_relat_1(C_619)) | ~v1_funct_1(C_619) | ~v1_relat_1(C_619))), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.57/4.36  tff(c_18904, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2'))) | ~r1_tarski('#skF_3', k1_relat_1('#skF_1')) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_17706, c_18871])).
% 11.57/4.36  tff(c_18933, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_17678, c_18904])).
% 11.57/4.36  tff(c_18943, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_14, c_18933])).
% 11.57/4.36  tff(c_18947, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_18943])).
% 11.57/4.36  tff(c_18949, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17735, c_18947])).
% 11.57/4.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.57/4.36  
% 11.57/4.36  Inference rules
% 11.57/4.36  ----------------------
% 11.57/4.36  #Ref     : 0
% 11.57/4.36  #Sup     : 4703
% 11.57/4.36  #Fact    : 0
% 11.57/4.36  #Define  : 0
% 11.57/4.36  #Split   : 16
% 11.57/4.36  #Chain   : 0
% 11.57/4.36  #Close   : 0
% 11.57/4.36  
% 11.57/4.36  Ordering : KBO
% 11.57/4.36  
% 11.57/4.36  Simplification rules
% 11.57/4.36  ----------------------
% 11.57/4.36  #Subsume      : 1054
% 11.57/4.36  #Demod        : 1537
% 11.57/4.36  #Tautology    : 977
% 11.57/4.36  #SimpNegUnit  : 7
% 11.57/4.36  #BackRed      : 3
% 11.57/4.36  
% 11.57/4.36  #Partial instantiations: 0
% 11.57/4.36  #Strategies tried      : 1
% 11.57/4.36  
% 11.57/4.36  Timing (in seconds)
% 11.57/4.36  ----------------------
% 11.57/4.36  Preprocessing        : 0.31
% 11.57/4.36  Parsing              : 0.17
% 11.57/4.36  CNF conversion       : 0.02
% 11.57/4.36  Main loop            : 3.28
% 11.57/4.36  Inferencing          : 0.71
% 11.57/4.36  Reduction            : 1.30
% 11.57/4.36  Demodulation         : 1.04
% 11.57/4.36  BG Simplification    : 0.09
% 11.57/4.36  Subsumption          : 0.96
% 11.57/4.36  Abstraction          : 0.13
% 11.57/4.36  MUC search           : 0.00
% 11.57/4.36  Cooper               : 0.00
% 11.57/4.36  Total                : 3.63
% 11.57/4.36  Index Insertion      : 0.00
% 11.57/4.36  Index Deletion       : 0.00
% 11.57/4.36  Index Matching       : 0.00
% 11.57/4.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
